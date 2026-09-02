import KakeyaNeedleC3C4.LeafCertificate5

/-!
# Compact binary certificate decoder

This module is intentionally only a deserializer.  Its output is an ordinary
typed certificate, which must still be accepted by the exact checkers in
`LeafCertificate`.  Consequently malformed input can at worst decode to
`none` or to a certificate which the checker rejects.

The wire format uses unsigned base-128 varints.  Signed integers use zig-zag
encoding, and a rational is encoded as its zig-zag numerator followed by
`denominator - 1`.  Lists are prefixed by their length.  Tags and booleans are
single bytes.  Finite indices are varints and are bounds checked.
-/

namespace KakeyaNeedleC3C4
namespace CertificateDecoder

open LeafCertificate

/-- Current position in an immutable byte buffer. -/
structure Cursor where
  bytes : ByteArray
  offset : Nat := 0

abbrev Decoder (α : Type) := StateT Cursor Option α

private def failure {α : Type} : Decoder α := fun _ => none

def remaining (c : Cursor) : Nat := c.bytes.size - c.offset

def readByte : Decoder UInt8 := fun c =>
  if h : c.offset < c.bytes.size then
    some (c.bytes[c.offset], { c with offset := c.offset + 1 })
  else
    none

/-- Decode a base-128 unsigned integer.  The fuel is the number of bytes
remaining, so even a non-terminating continuation sequence fails totally. -/
private def readVarNatFuel : Nat → Nat → Nat → Decoder Nat
  | 0, _, _ => failure
  | fuel + 1, place, acc => do
      let byte := (← readByte).toNat
      let acc' := acc + (byte % 128) * place
      if byte < 128 then
        pure acc'
      else
        readVarNatFuel fuel (place * 128) acc'

def readVarNat : Decoder Nat := fun c =>
  (readVarNatFuel (remaining c) 1 0) c

/-- Inverse of the usual zig-zag map `0,-1,1,-2,2,...`. -/
def zigZagDecode (n : Nat) : Int :=
  if n % 2 = 0 then
    Int.ofNat (n / 2)
  else
    -Int.ofNat (n / 2) - 1

def readInt : Decoder Int := zigZagDecode <$> readVarNat

def readRat : Decoder ℚ := do
  let numerator ← readInt
  let denominatorMinusOne ← readVarNat
  pure (Rat.normalize numerator (denominatorMinusOne + 1) (Nat.succ_ne_zero _))

def readBool : Decoder Bool := do
  match (← readByte).toNat with
  | 0 => pure false
  | 1 => pure true
  | _ => failure

def readFin (n : Nat) : Decoder (Fin n) := do
  let value ← readVarNat
  if h : value < n then
    pure ⟨value, h⟩
  else
    failure

private def readFixed {α : Type} : (count : Nat) → Decoder α → Decoder (List α)
  | 0, _ => pure []
  | count + 1, item => do
      let head ← item
      let tail ← readFixed count item
      pure (head :: tail)

/-- Length-prefixed list.  Every supported element consumes at least one
byte, so this early bound prevents hostile lengths from causing long loops. -/
def readList {α : Type} (item : Decoder α) : Decoder (List α) := do
  let count ← readVarNat
  let c ← get
  if count ≤ remaining c then
    readFixed count item
  else
    failure

private def arrayAtD {α : Type} (fallback : α) (xs : Array α) (i : Nat) : α :=
  xs[i]?.getD fallback

def readRationalAffine (n : Nat) : Decoder (RationalAffine n) := do
  let constant ← readRat
  let coefficients := (← readFixed n readRat).toArray
  pure {
    constant := constant
    linear := fun i => arrayAtD 0 coefficients i.1
  }

def readSparseFarkasCertificate (m : Nat) :
    Decoder (SparseFarkasCertificate m) := do
  let terms ← readList do
    let index ← readFin m
    let weight ← readRat
    pure (index, weight)
  pure { terms := terms }

def readHandelmanTerm (m : Nat) : Decoder (HandelmanTerm m) := do
  let left ← readFin (m + 1)
  let right ← readFin (m + 1)
  let weight ← readRat
  pure { left := left, right := right, weight := weight }

def readHandelmanCertificate (m : Nat) : Decoder (HandelmanCertificate m) := do
  let terms ← readList (readHandelmanTerm m)
  pure { terms := terms }

def readWeightedAffineSquare (n : Nat) : Decoder (WeightedAffineSquare n) := do
  let weight ← readRat
  let affine ← readRationalAffine n
  pure { weight := weight, affine := affine }

def readSOSHandelmanCertificate (n m : Nat) :
    Decoder (SOSHandelmanCertificate n m) := do
  let squares ← readList (readWeightedAffineSquare n)
  let products ← readHandelmanCertificate m
  pure { squares := squares, products := products }

private def emptySparse (m : Nat) : SparseFarkasCertificate m := { terms := [] }

private def defaultSlab3 (m : Nat) : SweepCertificate.Slab3 m where
  order := fun _ => 0
  overlap := fun _ => false
  orderCertificate := fun _ => emptySparse m
  overlapCertificate := fun _ => emptySparse m

private def defaultSlab4 (m : Nat) : SweepCertificate.Slab4 m where
  order := fun _ => 0
  overlap := fun _ => false
  orderCertificate := fun _ => emptySparse m
  overlapCertificate := fun _ => emptySparse m

private def defaultSlab5 (m : Nat) : SweepCertificate.Slab5 m where
  order := fun _ => 0
  overlap := fun _ => false
  orderCertificate := fun _ => emptySparse m
  overlapCertificate := fun _ => emptySparse m

def readSlab3 (m : Nat) : Decoder (SweepCertificate.Slab3 m) := do
  let order := (← readFixed 3 (readFin 3)).toArray
  let overlap := (← readFixed 2 readBool).toArray
  let orderCertificate :=
    (← readFixed 2 (readSparseFarkasCertificate m)).toArray
  let overlapCertificate :=
    (← readFixed 2 (readSparseFarkasCertificate m)).toArray
  pure {
    order := fun i => arrayAtD 0 order i.1
    overlap := fun i => arrayAtD false overlap i.1
    orderCertificate := fun i => arrayAtD (emptySparse m) orderCertificate i.1
    overlapCertificate := fun i => arrayAtD (emptySparse m) overlapCertificate i.1
  }

def readSlab4 (m : Nat) : Decoder (SweepCertificate.Slab4 m) := do
  let order := (← readFixed 4 (readFin 4)).toArray
  let overlap := (← readFixed 3 readBool).toArray
  let orderCertificate :=
    (← readFixed 3 (readSparseFarkasCertificate m)).toArray
  let overlapCertificate :=
    (← readFixed 3 (readSparseFarkasCertificate m)).toArray
  pure {
    order := fun i => arrayAtD 0 order i.1
    overlap := fun i => arrayAtD false overlap i.1
    orderCertificate := fun i => arrayAtD (emptySparse m) orderCertificate i.1
    overlapCertificate := fun i => arrayAtD (emptySparse m) overlapCertificate i.1
  }

def readSlab5 (m : Nat) : Decoder (SweepCertificate.Slab5 m) := do
  let order := (← readFixed 5 (readFin 5)).toArray
  let overlap := (← readFixed 4 readBool).toArray
  let orderCertificate :=
    (← readFixed 4 (readSparseFarkasCertificate m)).toArray
  let overlapCertificate :=
    (← readFixed 4 (readSparseFarkasCertificate m)).toArray
  pure {
    order := fun i => arrayAtD 0 order i.1
    overlap := fun i => arrayAtD false overlap i.1
    orderCertificate := fun i => arrayAtD (emptySparse m) orderCertificate i.1
    overlapCertificate := fun i => arrayAtD (emptySparse m) overlapCertificate i.1
  }

def readSweepCertificate3 (m : Nat) :
    Decoder (SweepCertificate.Certificate3 m) := do
  let slabCount ← readVarNat
  let breakpoint :=
    (← readFixed (slabCount + 1) (readRationalAffine 3)).toArray
  let breakpointOrderCertificate :=
    (← readFixed slabCount (readSparseFarkasCertificate m)).toArray
  let slab := (← readFixed slabCount (readSlab3 m)).toArray
  pure {
    slabCount := slabCount
    breakpoint := fun i =>
      arrayAtD (SweepCertificate.affineZero 3) breakpoint i.1
    breakpointOrderCertificate := fun i =>
      arrayAtD (emptySparse m) breakpointOrderCertificate i.1
    slab := fun i => arrayAtD (defaultSlab3 m) slab i.1
  }

def readSweepCertificate4 (m : Nat) :
    Decoder (SweepCertificate.Certificate4 m) := do
  let slabCount ← readVarNat
  let breakpoint :=
    (← readFixed (slabCount + 1) (readRationalAffine 4)).toArray
  let breakpointOrderCertificate :=
    (← readFixed slabCount (readSparseFarkasCertificate m)).toArray
  let slab := (← readFixed slabCount (readSlab4 m)).toArray
  pure {
    slabCount := slabCount
    breakpoint := fun i =>
      arrayAtD (SweepCertificate.affineZero 4) breakpoint i.1
    breakpointOrderCertificate := fun i =>
      arrayAtD (emptySparse m) breakpointOrderCertificate i.1
    slab := fun i => arrayAtD (defaultSlab4 m) slab i.1
  }

def readSweepCertificate5 (m : Nat) :
    Decoder (SweepCertificate.Certificate5 m) := do
  let slabCount ← readVarNat
  let breakpoint :=
    (← readFixed (slabCount + 1) (readRationalAffine 5)).toArray
  let breakpointOrderCertificate :=
    (← readFixed slabCount (readSparseFarkasCertificate m)).toArray
  let slab := (← readFixed slabCount (readSlab5 m)).toArray
  pure {
    slabCount := slabCount
    breakpoint := fun i =>
      arrayAtD (SweepCertificate.affineZero 5) breakpoint i.1
    breakpointOrderCertificate := fun i =>
      arrayAtD (emptySparse m) breakpointOrderCertificate i.1
    slab := fun i => arrayAtD (defaultSlab5 m) slab i.1
  }

/-- Leaf tags: `0 = empty`, `1 = live`, `2 = liveSOS`. -/
def readLeaf3 (m : Nat) : Decoder (Leaf3 m) := do
  match (← readByte).toNat with
  | 0 => Leaf3.empty <$> readSparseFarkasCertificate m
  | 1 => Leaf3.live <$> readSweepCertificate3 m <*>
      readHandelmanCertificate m
  | 2 => Leaf3.liveSOS <$> readSweepCertificate3 m <*>
      readSOSHandelmanCertificate 3 m
  | _ => failure

def readLeaf4 (m : Nat) : Decoder (Leaf4 m) := do
  match (← readByte).toNat with
  | 0 => Leaf4.empty <$> readSparseFarkasCertificate m
  | 1 => Leaf4.live <$> readSweepCertificate4 m <*>
      readHandelmanCertificate m
  | 2 => Leaf4.liveSOS <$> readSweepCertificate4 m <*>
      readSOSHandelmanCertificate 4 m
  | _ => failure

def readLeaf5 (m : Nat) : Decoder (Leaf5 m) := do
  match (← readByte).toNat with
  | 0 => Leaf5.empty <$> readSparseFarkasCertificate m
  | 1 => Leaf5.live <$> readSweepCertificate5 m <*>
      readHandelmanCertificate m
  | 2 => Leaf5.liveSOS <$> readSweepCertificate5 m <*>
      readSOSHandelmanCertificate 5 m
  | _ => failure

/-- Tree tags: `0 = leaf`, `1 = branch`.  Fuel bounds malformed deeply nested
inputs by the number of bytes in the original buffer. -/
private def readPayloadTreeFuel {α : Type} (H : Nat) (readPayload : Decoder α) :
    Nat → Decoder (PayloadTree H α)
  | 0 => failure
  | fuel + 1 => do
      match (← readByte).toNat with
      | 0 => PayloadTree.leaf <$> readPayload
      | 1 =>
          let wall ← readFin H
          let pos ← readPayloadTreeFuel H readPayload fuel
          let neg ← readPayloadTreeFuel H readPayload fuel
          pure (.branch wall pos neg)
      | _ => failure

def readPayloadTree {α : Type} (H : Nat) (readPayload : Decoder α) :
    Decoder (PayloadTree H α) := do
  let c ← get
  readPayloadTreeFuel H readPayload (remaining c + 1)

def readTree3 (H m : Nat) : Decoder (Tree3 H m) :=
  readPayloadTree H (readLeaf3 m)

def readTree4 (H m : Nat) : Decoder (Tree4 H m) :=
  readPayloadTree H (readLeaf4 m)

def readTree5 (H m : Nat) : Decoder (Tree5 H m) :=
  readPayloadTree H (readLeaf5 m)

/-- Run a decoder and reject trailing bytes. -/
def decodeAll (decoder : Decoder α) (bytes : ByteArray) : Option α := do
  let (value, finalCursor) ← decoder { bytes := bytes }
  if finalCursor.offset = bytes.size then pure value else none

def decodeTree3 (H m : Nat) (bytes : ByteArray) : Option (Tree3 H m) :=
  decodeAll (readTree3 H m) bytes

def decodeTree4 (H m : Nat) (bytes : ByteArray) : Option (Tree4 H m) :=
  decodeAll (readTree4 H m) bytes

def decodeTree5 (H m : Nat) (bytes : ByteArray) : Option (Tree5 H m) :=
  decodeAll (readTree5 H m) bytes

/-! ## Text embedding

Lean currently provides `include_str` but no corresponding binary-file term.
The generator can therefore emit the compact bytes as unpadded Base64 (or,
more simply, hexadecimal), embed that file with `include_str`, and decode the
string at run time.  This is still one string literal in the environment
rather than millions of syntax-tree nodes.  Base64 costs 4/3 of the binary
size; hexadecimal costs twice the binary size.
-/

private def hexNibble (byte : UInt8) : Option Nat :=
  let n := byte.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n - 48)
  else if 65 ≤ n ∧ n ≤ 70 then some (n - 65 + 10)
  else if 97 ≤ n ∧ n ≤ 102 then some (n - 97 + 10)
  else none

private def isAsciiWhitespace (byte : UInt8) : Bool :=
  byte = 9 || byte = 10 || byte = 13 || byte = 32

private def decodeHexFuel : Nat → ByteArray → Nat → Option Nat → ByteArray →
    Option ByteArray
  | 0, input, offset, pending, output =>
      if offset = input.size then
        if pending.isNone then some output else none
      else none
  | fuel + 1, input, offset, pending, output =>
      if h : offset < input.size then
        let byte := input[offset]
        if isAsciiWhitespace byte then
          decodeHexFuel fuel input (offset + 1) pending output
        else
          match hexNibble byte with
          | none => none
          | some nibble =>
              match pending with
              | none => decodeHexFuel fuel input (offset + 1) (some nibble) output
              | some high =>
                  decodeHexFuel fuel input (offset + 1) none
                    (output.push (UInt8.ofNat (16 * high + nibble)))
      else
        if pending.isNone then some output else none

/-- Decode an ASCII hexadecimal string; spaces and line breaks are ignored. -/
def decodeHex (text : String) : Option ByteArray :=
  let input := text.toUTF8
  decodeHexFuel (input.size + 1) input 0 none ByteArray.empty

private def base64Sextet (byte : UInt8) : Option Nat :=
  let n := byte.toNat
  if 65 ≤ n ∧ n ≤ 90 then some (n - 65)
  else if 97 ≤ n ∧ n ≤ 122 then some (n - 97 + 26)
  else if 48 ≤ n ∧ n ≤ 57 then some (n - 48 + 52)
  else if n = 43 then some 62
  else if n = 47 then some 63
  else none

/-- Streaming decoder for unpadded RFC 4648 Base64.  At most twelve pending
bits are held, so the `Nat` accumulator remains tiny. -/
private def decodeBase64Fuel : Nat → ByteArray → Nat → Nat → Nat → ByteArray →
    Option ByteArray
  | 0, input, offset, buffer, bitCount, output =>
      if offset = input.size ∧ (bitCount = 0 ∨
          ((bitCount = 2 ∨ bitCount = 4) ∧ buffer = 0)) then
        some output
      else none
  | fuel + 1, input, offset, buffer, bitCount, output =>
      if h : offset < input.size then
        let byte := input[offset]
        if isAsciiWhitespace byte then
          decodeBase64Fuel fuel input (offset + 1) buffer bitCount output
        else
          match base64Sextet byte with
          | none => none
          | some sextet =>
              let combined := buffer * 64 + sextet
              let combinedBits := bitCount + 6
              if 8 ≤ combinedBits then
                let remainingBits := combinedBits - 8
                let divisor := 2 ^ remainingBits
                let decoded := (combined / divisor) % 256
                decodeBase64Fuel fuel input (offset + 1) (combined % divisor)
                  remainingBits (output.push (UInt8.ofNat decoded))
              else
                decodeBase64Fuel fuel input (offset + 1) combined combinedBits output
      else if bitCount = 0 ∨ ((bitCount = 2 ∨ bitCount = 4) ∧ buffer = 0) then
        some output
      else none

/-- Decode standard-alphabet Base64 without `=` padding.  ASCII whitespace is
ignored.  Python generators can use `base64.b64encode(data).decode().rstrip('=')`. -/
def decodeBase64 (text : String) : Option ByteArray :=
  let input := text.toUTF8
  decodeBase64Fuel (input.size + 1) input 0 0 0 ByteArray.empty

/-! ## Decode-and-check wrappers

These wrappers deliberately return `false` on every decoding failure.  Thus a
single `native_decide` proof checks both successful deserialization and the
entire exact certificate tree; it never substitutes a fallback tree.
-/

def checkEncodedTree3 {H m : Nat} (maxDepth : Nat)
    (polyForPath : List (SignedIndex H) → RationalPolyhedron 3 m)
    (target : ℚ) (encoded : String) : Bool :=
  match decodeBase64 encoded >>= decodeTree3 H m with
  | none => false
  | some tree => checkTree3 maxDepth polyForPath target tree

def checkEncodedTree4 {H m : Nat} (maxDepth : Nat)
    (polyForPath : List (SignedIndex H) → RationalPolyhedron 4 m)
    (target : ℚ) (encoded : String) : Bool :=
  match decodeBase64 encoded >>= decodeTree4 H m with
  | none => false
  | some tree => checkTree4 maxDepth polyForPath target tree

def treeLeafCount {H : Nat} {α : Type} : PayloadTree H α → Nat
  | .leaf _ => 1
  | .branch _ pos neg => treeLeafCount pos + treeLeafCount neg

/-- Decode and check an n=5 tree while also checking that the same proof
payload has the notebook's declared number of arrangement cells. -/
def checkEncodedTree5 {H m : Nat} (maxDepth expectedCells : Nat)
    (polyForPath : List (SignedIndex H) → RationalPolyhedron 5 m)
    (target : ℚ) (encoded : String) : Bool :=
  match decodeBase64 encoded >>= decodeTree5 H m with
  | none => false
  | some tree => checkTree5 maxDepth polyForPath target tree &&
      decide (treeLeafCount tree = expectedCells)

theorem checkEncodedTree3_sound {H m : Nat} {maxDepth : Nat}
    {walls : Fin H → RationalAffine 3}
    {polyForPath : List (SignedIndex H) → RationalPolyhedron 3 m}
    {target : ℚ} {encoded : String} {Base : (Fin 3 → ℝ) → Prop}
    (hcarrier : ∀ p path, path.length ≤ maxDepth →
      PathNonnegative walls p path → Base p →
      p ∈ (polyForPath path).carrier)
    (hcheck : checkEncodedTree3 maxDepth polyForPath target encoded = true) :
    ∀ p, Base p → (target : ℝ) ≤ unionArea 3 p := by
  generalize hdecode : (decodeBase64 encoded >>= decodeTree3 H m) = decoded
  cases decoded with
  | none => simp [checkEncodedTree3, hdecode] at hcheck
  | some tree =>
      apply LeafCertificate.checkTree3_sound hcarrier
      simpa [checkEncodedTree3, hdecode] using hcheck

theorem checkEncodedTree4_sound {H m : Nat} {maxDepth : Nat}
    {walls : Fin H → RationalAffine 4}
    {polyForPath : List (SignedIndex H) → RationalPolyhedron 4 m}
    {target : ℚ} {encoded : String} {Base : (Fin 4 → ℝ) → Prop}
    (hcarrier : ∀ p path, path.length ≤ maxDepth →
      PathNonnegative walls p path → Base p →
      p ∈ (polyForPath path).carrier)
    (hcheck : checkEncodedTree4 maxDepth polyForPath target encoded = true) :
    ∀ p, Base p → (target : ℝ) ≤ unionArea 4 p := by
  generalize hdecode : (decodeBase64 encoded >>= decodeTree4 H m) = decoded
  cases decoded with
  | none => simp [checkEncodedTree4, hdecode] at hcheck
  | some tree =>
      apply LeafCertificate.checkTree4_sound hcarrier
      simpa [checkEncodedTree4, hdecode] using hcheck

theorem checkEncodedTree5_sound {H m : Nat} {maxDepth expectedCells : Nat}
    {walls : Fin H → RationalAffine 5}
    {polyForPath : List (SignedIndex H) → RationalPolyhedron 5 m}
    {target : ℚ} {encoded : String} {Base : (Fin 5 → ℝ) → Prop}
    (hcarrier : ∀ p path, path.length ≤ maxDepth →
      PathNonnegative walls p path → Base p →
      p ∈ (polyForPath path).carrier)
    (hcheck : checkEncodedTree5 maxDepth expectedCells polyForPath target
      encoded = true) :
    ∀ p, Base p → (target : ℝ) ≤ unionArea 5 p := by
  generalize hdecode : (decodeBase64 encoded >>= decodeTree5 H m) = decoded
  cases decoded with
  | none => simp [checkEncodedTree5, hdecode] at hcheck
  | some tree =>
      simp only [checkEncodedTree5, hdecode, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      apply LeafCertificate.checkTree5_sound hcarrier
      exact hcheck.1

theorem checkEncodedTree5_cellCount {H m : Nat} {maxDepth expectedCells : Nat}
    {polyForPath : List (SignedIndex H) → RationalPolyhedron 5 m}
    {target : ℚ} {encoded : String}
    (hcheck : checkEncodedTree5 maxDepth expectedCells polyForPath target
      encoded = true) :
    ∃ tree, decodeBase64 encoded >>= decodeTree5 H m = some tree ∧
      treeLeafCount tree = expectedCells := by
  generalize hdecode : (decodeBase64 encoded >>= decodeTree5 H m) = decoded
  cases decoded with
  | none => simp [checkEncodedTree5, hdecode] at hcheck
  | some tree =>
      simp only [checkEncodedTree5, hdecode, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      exact ⟨tree, rfl, hcheck.2⟩

/-! ## Compact subtree wrappers

The large four-needle certificate is split below a shallow decision-tree
frontier.  Each encoded subtree is checked with the exact structural prefix
already accumulated above it, then decoded for a lightweight stitched root.
-/

private def fallbackTree4 {H m : Nat} : Tree4 H m :=
  .leaf (.empty { terms := [] })

def decodedEncodedTree4 {H m : Nat} (encoded : String) : Tree4 H m :=
  match decodeBase64 encoded >>= decodeTree4 H m with
  | none => fallbackTree4
  | some tree => tree

def checkEncodedTreeAux4 {H m : Nat} (maxDepth : Nat)
    (polyForPath : List (SignedIndex H) → RationalPolyhedron 4 m)
    (target : ℚ) (current : List (SignedIndex H)) (encoded : String) : Bool :=
  match decodeBase64 encoded >>= decodeTree4 H m with
  | none => false
  | some tree => checkTreeAux4 maxDepth polyForPath target current tree

theorem checkEncodedTreeAux4_as_decoded {H m : Nat} {maxDepth : Nat}
    {polyForPath : List (SignedIndex H) → RationalPolyhedron 4 m}
    {target : ℚ} {current : List (SignedIndex H)} {encoded : String}
    (hcheck : checkEncodedTreeAux4 maxDepth polyForPath target current encoded = true) :
    checkTreeAux4 maxDepth polyForPath target current
      (decodedEncodedTree4 encoded) = true := by
  generalize hdecode : (decodeBase64 encoded >>= decodeTree4 H m) = decoded
  cases decoded with
  | none => simp [checkEncodedTreeAux4, hdecode] at hcheck
  | some tree =>
      simpa [checkEncodedTreeAux4, decodedEncodedTree4, hdecode] using hcheck

/-! A small executable smoke test.  The six bytes encode a tree leaf, an
empty-leaf tag, and the singleton sparse certificate `[(0, 1)]`. -/

private def smokeExpected : Tree4 1 1 :=
  .leaf (.empty { terms := [(⟨0, by decide⟩, 1)] })

private def smokePolyForPath
    (_ : List (SignedIndex 1)) : RationalPolyhedron 4 1 where
  constraint := fun _ => { constant := -1, linear := fun _ => 0 }

example : decodeTree4 1 1 (ByteArray.mk #[0, 0, 1, 0, 2, 0]) =
    some smokeExpected := by
  native_decide

example : (decodeHex "00 00 01 00 02 00\n" >>= decodeTree4 1 1) =
    some smokeExpected := by
  native_decide

example : (decodeBase64 "AAABAAIA\n" >>= decodeTree4 1 1) =
    some smokeExpected := by
  native_decide

example : checkEncodedTree4 0 smokePolyForPath 1 "AAABAAIA" = true := by
  native_decide

example : decodeTree4 1 1 (ByteArray.mk #[0, 0, 1, 0, 2]) = none := by
  native_decide

end CertificateDecoder
end KakeyaNeedleC3C4
