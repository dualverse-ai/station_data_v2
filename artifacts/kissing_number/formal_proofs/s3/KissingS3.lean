import Mathlib

/-!
# Spotlight 3: the signed weight-four shell

This file formalizes the signed-shell identity from the kissing-number section:
allowing signs on four-coordinate supports multiplies the optimum by exactly 16.
-/

namespace KissingS3

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

/-- A four-coordinate support. -/
structure Support4 (ι : Type*) [DecidableEq ι] where
  carrier : Finset ι
  card_eq : carrier.card = 4

instance : DecidableEq (Support4 ι) := fun S T =>
  if h : S.carrier = T.carrier then
    isTrue (by cases S; cases T; cases h; rfl)
  else isFalse (fun h' => h (congrArg Support4.carrier h'))

@[ext] lemma Support4.extensionality (S T : Support4 ι)
    (h : S.carrier = T.carrier) : S = T := by
  cases S
  cases T
  simp_all

/-- A signed weight-four row, encoded by the subset of its support carrying a minus sign. -/
structure SignedSupport (ι : Type*) [DecidableEq ι] where
  support : Support4 ι
  negative : Finset ι
  negative_subset : negative ⊆ support.carrier

instance : DecidableEq (SignedSupport ι) := fun r s =>
  if hs : r.support = s.support then
    if hn : r.negative = s.negative then
      isTrue (by cases r; cases s; cases hs; cases hn; rfl)
    else isFalse (fun h => hn (congrArg SignedSupport.negative h))
  else isFalse (fun h => hs (congrArg SignedSupport.support h))

/-- Ordinary compatibility of four-subsets: distinct supports meet in at most two places. -/
def SupportCompatible (F : Finset (Support4 ι)) : Prop :=
  ∀ S ∈ F, ∀ T ∈ F, S ≠ T → (S.carrier ∩ T.carrier).card ≤ 2

instance (F : Finset (Support4 ι)) : Decidable (SupportCompatible F) := by
  unfold SupportCompatible
  infer_instance

/-- Signed compatibility.  If two distinct supports carry the same signs on their
intersection, that intersection has size at most two.  This is exactly the condition
that the associated signed weight-four vectors have inner product at most two. -/
def SignedCompatible (C : Finset (SignedSupport ι)) : Prop :=
  ∀ r ∈ C, ∀ s ∈ C, r.support ≠ s.support →
    r.negative ∩ s.support.carrier = s.negative ∩ r.support.carrier →
    (r.support.carrier ∩ s.support.carrier).card ≤ 2

instance (C : Finset (SignedSupport ι)) : Decidable (SignedCompatible C) := by
  unfold SignedCompatible
  infer_instance

/-- Coordinates on which two signed rows are both nonzero. -/
def commonSupport (r s : SignedSupport ι) : Finset ι :=
  r.support.carrier ∩ s.support.carrier

/-- Coordinates in the common support where the two signs agree. -/
def signAgreements (r s : SignedSupport ι) : Finset ι :=
  (commonSupport r s).filter (fun i => (i ∈ r.negative) = (i ∈ s.negative))

/-- Coordinates in the common support where the two signs disagree. -/
def signDisagreements (r s : SignedSupport ι) : Finset ι :=
  (commonSupport r s).filter (fun i => (i ∈ r.negative) ≠ (i ∈ s.negative))

/-- The ordinary integer dot product of the associated vectors: agreeing
coordinates contribute `+1`, disagreeing coordinates contribute `-1`. -/
def signedInnerProduct (r s : SignedSupport ι) : ℤ :=
  (signAgreements r s).card - (signDisagreements r s).card

lemma agreement_disagreement_card (r s : SignedSupport ι) :
    (signAgreements r s).card + (signDisagreements r s).card =
      (commonSupport r s).card := by
  classical
  simpa [signAgreements, signDisagreements] using
    (Finset.filter_card_add_filter_neg_card_eq_card
      (s := commonSupport r s) (fun i => (i ∈ r.negative) = (i ∈ s.negative)))

lemma no_sign_disagreements_iff (r s : SignedSupport ι) :
    (signDisagreements r s).card = 0 ↔
      r.negative ∩ s.support.carrier = s.negative ∩ r.support.carrier := by
  classical
  rw [Finset.card_eq_zero]
  constructor
  · intro h
    apply Finset.ext
    intro x
    have hx : x ∉ signDisagreements r s := by simp [h]
    by_cases hrs : x ∈ commonSupport r s
    · have hagree : (x ∈ r.negative) = (x ∈ s.negative) := by
        by_cases hrn : x ∈ r.negative <;> by_cases hsn : x ∈ s.negative <;>
          simp_all [signDisagreements]
      simp only [Finset.mem_inter]
      have hrs' : x ∈ r.support.carrier ∧ x ∈ s.support.carrier := by
        simpa [commonSupport] using hrs
      simp [hrs'.1, hrs'.2, hagree]
    · have hnot : x ∉ r.support.carrier ∨ x ∉ s.support.carrier := by
        simp only [commonSupport, Finset.mem_inter] at hrs
        exact not_and_or.mp hrs
      rcases hnot with hr | hs
      · have hn : x ∉ r.negative := fun hx => hr (r.negative_subset hx)
        simp [hr, hn]
      · have hn : x ∉ s.negative := fun hx => hs (s.negative_subset hx)
        simp [hs, hn]
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxcommon : x ∈ commonSupport r s := by
      exact (Finset.mem_filter.mp hx).1
    have hne := (Finset.mem_filter.mp hx).2
    have hrs : x ∈ r.support.carrier ∧ x ∈ s.support.carrier := by
      simpa [commonSupport] using hxcommon
    have heq := Finset.ext_iff.mp h x
    simp [hrs.1, hrs.2] at heq
    exact hne (propext heq)

lemma common_support_card_le_three {r s : SignedSupport ι}
    (hrs : r.support ≠ s.support) : (commonSupport r s).card ≤ 3 := by
  have hleR : (commonSupport r s).card ≤ r.support.carrier.card :=
    Finset.card_le_card Finset.inter_subset_left
  have hleS : (commonSupport r s).card ≤ s.support.carrier.card :=
    Finset.card_le_card Finset.inter_subset_right
  by_contra h
  have hcard : (commonSupport r s).card = 4 := by
    rw [r.support.card_eq] at hleR
    omega
  have heqR : commonSupport r s = r.support.carrier :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
      rw [r.support.card_eq, hcard])
  have heqS : commonSupport r s = s.support.carrier :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
      rw [s.support.card_eq, hcard])
  apply hrs
  exact Support4.extensionality _ _ (heqR.symm.trans heqS)

/-- The combinatorial definition of `SignedCompatible` is exactly the kissing
inequality `dot ≤ 2` for distinct signed weight-four rows. -/
theorem signed_compatible_iff_inner_product (C : Finset (SignedSupport ι)) :
    SignedCompatible C ↔
      ∀ r ∈ C, ∀ s ∈ C, r ≠ s → signedInnerProduct r s ≤ 2 := by
  constructor
  · intro hC r hr s hs hrs
    have hpartition := agreement_disagreement_card r s
    by_cases hsupport : r.support = s.support
    · have hneg : r.negative ≠ s.negative := by
        intro hn
        apply hrs
        cases r
        cases s
        simp_all
      have hdis : 1 ≤ (signDisagreements r s).card := by
        by_contra hzero
        have hz : (signDisagreements r s).card = 0 := by omega
        have heq := (no_sign_disagreements_iff r s).mp hz
        apply hneg
        have hrsub : r.negative ⊆ s.support.carrier := by
          rw [← hsupport]
          exact r.negative_subset
        have hssub : s.negative ⊆ r.support.carrier := by
          rw [hsupport]
          exact s.negative_subset
        rw [Finset.inter_eq_left.mpr hrsub, Finset.inter_eq_left.mpr hssub] at heq
        exact heq
      have hcommon : (commonSupport r s).card = 4 := by
        rw [commonSupport, hsupport, Finset.inter_self, s.support.card_eq]
      rw [hcommon] at hpartition
      simp only [signedInnerProduct]
      omega
    · have hcommon : (commonSupport r s).card ≤ 3 := common_support_card_le_three hsupport
      by_cases hagree : r.negative ∩ s.support.carrier = s.negative ∩ r.support.carrier
      · have htwo := hC r hr s hs hsupport hagree
        have hz := (no_sign_disagreements_iff r s).mpr hagree
        change (commonSupport r s).card ≤ 2 at htwo
        simp only [signedInnerProduct]
        omega
      · have hdis : 1 ≤ (signDisagreements r s).card := by
          have := (no_sign_disagreements_iff r s).not.mpr hagree
          omega
        simp only [signedInnerProduct]
        omega
  · intro hdot r hr s hs hsupport hagree
    have hne : r ≠ s := fun h => hsupport (congrArg SignedSupport.support h)
    have hdot' := hdot r hr s hs hne
    have hz := (no_sign_disagreements_iff r s).mpr hagree
    have hpartition := agreement_disagreement_card r s
    simp only [signedInnerProduct] at hdot'
    change (commonSupport r s).card ≤ 2
    omega

/-- `A` is the exact maximum size of a compatible family of four-supports. -/
def IsSupportMaximum (A : ℕ) : Prop :=
  (∀ F : Finset (Support4 ι), SupportCompatible F → F.card ≤ A) ∧
  ∃ F : Finset (Support4 ι), SupportCompatible F ∧ F.card = A

/-- `M` is the exact maximum size of a compatible family of signed supports. -/
def IsSignedMaximum (M : ℕ) : Prop :=
  (∀ C : Finset (SignedSupport ι), SignedCompatible C → C.card ≤ M) ∧
  ∃ C : Finset (SignedSupport ι), SignedCompatible C ∧ C.card = M

/-- A global sign set extends a signed row when it has exactly the prescribed
negative coordinates on the row's support. -/
def Extends (g : Finset ι) (r : SignedSupport ι) : Prop :=
  g ∩ r.support.carrier = r.negative

instance (g : Finset ι) : DecidablePred (Extends g (ι := ι)) :=
  fun r => inferInstanceAs (Decidable (g ∩ r.support.carrier = r.negative))

lemma card_global_extensions (U : Finset ι) (r : SignedSupport ι)
    (hrU : r.support.carrier ⊆ U) :
    (U.powerset.filter (fun g => Extends g r)).card = 2 ^ (U.card - 4) := by
  classical
  let outside := U \ r.support.carrier
  have hcard : outside.card = U.card - 4 := by
    rw [show outside = U \ r.support.carrier by rfl, Finset.card_sdiff,
      Finset.inter_eq_left.mpr hrU, r.support.card_eq]
  calc
    (U.powerset.filter (fun g => Extends g r)).card = outside.powerset.card := by
      symm
      apply Finset.card_bij (fun q _ => r.negative ∪ q)
      · intro q hq
        simp only [Finset.mem_powerset] at hq
        rw [Finset.mem_filter]
        constructor
        · rw [Finset.mem_powerset]
          exact Finset.union_subset (r.negative_subset.trans hrU)
            (hq.trans Finset.sdiff_subset)
        · apply Finset.ext
          intro x
          simp only [Finset.mem_inter, Finset.mem_union]
          constructor
          · rintro ⟨hxneg | hxq, _⟩
            · exact hxneg
            · have := hq hxq
              simp only [outside, Finset.mem_sdiff] at this
              exact (this.2 ‹x ∈ r.support.carrier›).elim
          · intro hxneg
            exact ⟨Or.inl hxneg, r.negative_subset hxneg⟩
      · intro q₁ hq₁ q₂ hq₂ heq
        apply Finset.ext
        intro x
        have hq₁' := (Finset.mem_powerset.mp hq₁)
        have hq₂' := (Finset.mem_powerset.mp hq₂)
        constructor
        · intro hx
          have hxout := hq₁' hx
          have hxnot : x ∉ r.support.carrier := (Finset.mem_sdiff.mp hxout).2
          have hxneg : x ∉ r.negative := fun h => hxnot (r.negative_subset h)
          have : x ∈ r.negative ∪ q₂ := by simpa [heq] using (show x ∈ r.negative ∪ q₁ by simp [hx])
          simpa [hxneg] using this
        · intro hx
          have hxout := hq₂' hx
          have hxnot : x ∉ r.support.carrier := (Finset.mem_sdiff.mp hxout).2
          have hxneg : x ∉ r.negative := fun h => hxnot (r.negative_subset h)
          have : x ∈ r.negative ∪ q₁ := by simpa [heq] using (show x ∈ r.negative ∪ q₂ by simp [hx])
          simpa [hxneg] using this
      · intro g hg
        simp only [Finset.mem_filter, Finset.mem_powerset] at hg
        refine ⟨g \ r.support.carrier, ?_, ?_⟩
        · simp only [Finset.mem_powerset, outside]
          exact Finset.sdiff_subset_sdiff hg.1 (by rfl)
        · apply Finset.ext
          intro x
          by_cases hx : x ∈ r.support.carrier
          · have hext : x ∈ g ↔ x ∈ r.negative := by
              have := Finset.ext_iff.mp hg.2 x
              simpa [Extends, hx] using this
            simp [hx, hext]
          · have hxneg : x ∉ r.negative := fun h => hx (r.negative_subset h)
            simp [hx, hxneg]
    _ = 2 ^ (U.card - 4) := by simp [hcard]

def visibleRows (g : Finset ι) (C : Finset (SignedSupport ι)) :
    Finset (SignedSupport ι) :=
  C.filter (Extends g)

def visibleSupports (g : Finset ι) (C : Finset (SignedSupport ι)) :
    Finset (Support4 ι) :=
  (visibleRows g C).image SignedSupport.support

lemma card_visibleSupports (g : Finset ι) (C : Finset (SignedSupport ι)) :
    (visibleSupports g C).card = (visibleRows g C).card := by
  classical
  apply Finset.card_image_iff.mpr
  intro r hr s hs hrs
  have hr' : r ∈ C ∧ Extends g r := by simpa [visibleRows] using hr
  have hs' : s ∈ C ∧ Extends g s := by simpa [visibleRows] using hs
  have her : Extends g r := hr'.2
  have hes : Extends g s := hs'.2
  have hn : r.negative = s.negative := by
    rw [← her, ← hes, hrs]
  cases r
  cases s
  simp_all

lemma visible_supports_compatible {g : Finset ι} {C : Finset (SignedSupport ι)}
    (hC : SignedCompatible C) : SupportCompatible (visibleSupports g C) := by
  classical
  intro R hR S hS hRS
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hR
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hS
  have hr' : r ∈ C ∧ Extends g r := by simpa [visibleRows] using hr
  have hs' : s ∈ C ∧ Extends g s := by simpa [visibleRows] using hs
  have hrC : r ∈ C := hr'.1
  have hsC : s ∈ C := hs'.1
  have her : Extends g r := hr'.2
  have hes : Extends g s := hs'.2
  apply hC r hrC s hsC hRS
  calc
    r.negative ∩ s.support.carrier =
        (g ∩ r.support.carrier) ∩ s.support.carrier := by rw [her]
    _ = (g ∩ s.support.carrier) ∩ r.support.carrier := by
      ext x
      simp only [Finset.mem_inter]
      aesop
    _ = s.negative ∩ r.support.carrier := by rw [hes]

/-- The global-sign double count: any upper bound for unsigned four-support
families, multiplied by 16, bounds every compatible signed family. -/
theorem signed_shell_upper [Fintype ι] (A : ℕ) (hn : 4 ≤ Fintype.card ι)
    (hA : ∀ F : Finset (Support4 ι), SupportCompatible F → F.card ≤ A)
    (C : Finset (SignedSupport ι)) (hC : SignedCompatible C) :
    C.card ≤ 16 * A := by
  classical
  let G : Finset (Finset ι) := Finset.univ.powerset
  let e : ℕ := 2 ^ (Fintype.card ι - 4)
  have hdouble :
      (∑ g ∈ G, (visibleRows g C).card) = e * C.card := by
    calc
      (∑ g ∈ G, (visibleRows g C).card) =
          ∑ g ∈ G, ∑ r ∈ C, if Extends g r then 1 else 0 := by
            simp only [visibleRows, Finset.card_filter]
      _ = ∑ r ∈ C, ∑ g ∈ G, if Extends g r then 1 else 0 :=
        Finset.sum_comm
      _ = ∑ r ∈ C, (G.filter (fun g => Extends g r)).card := by
        simp only [Finset.card_filter]
      _ = ∑ _r ∈ C, e := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [show G = Finset.univ.powerset by rfl]
        exact card_global_extensions Finset.univ r (Finset.subset_univ _)
      _ = e * C.card := by simp [mul_comm]
  have hslice : ∀ g ∈ G, (visibleRows g C).card ≤ A := by
    intro g hg
    rw [← card_visibleSupports]
    exact hA _ (visible_supports_compatible hC)
  have htotal : e * C.card ≤ 2 ^ Fintype.card ι * A := by
    rw [← hdouble]
    calc
      (∑ g ∈ G, (visibleRows g C).card) ≤ ∑ _g ∈ G, A := by
        exact Finset.sum_le_sum fun g hg => hslice g hg
      _ = G.card * A := by simp
      _ = 2 ^ Fintype.card ι * A := by simp [G]
  have hpow : 2 ^ Fintype.card ι = e * 16 := by
    rw [show Fintype.card ι = (Fintype.card ι - 4) + 4 by omega, pow_add]
    norm_num [e]
  apply Nat.le_of_mul_le_mul_left (c := e)
  · calc
      e * C.card ≤ 2 ^ Fintype.card ι * A := htotal
      _ = e * (16 * A) := by rw [hpow]; simp [Nat.mul_assoc]
  · positivity

/-- One of the sixteen local sign choices on a four-support. -/
abbrev SigningChoice (S : Support4 ι) :=
  {N : Finset ι // N ∈ S.carrier.powerset}

def signingChoices (S : Support4 ι) : Finset (SigningChoice S) :=
  S.carrier.powerset.attach

def signedChoiceEmbedding :
    ((S : Support4 ι) × SigningChoice S) ↪ SignedSupport ι where
  toFun p :=
    { support := p.1
      negative := p.2.1
      negative_subset := Finset.mem_powerset.mp p.2.2 }
  inj' := by
    rintro ⟨S, N⟩ ⟨T, M⟩ h
    have hs : S = T := congrArg SignedSupport.support h
    subst T
    have hn : N.1 = M.1 := congrArg SignedSupport.negative h
    have hNM : N = M := Subtype.ext hn
    subst M
    rfl

/-- Put all sixteen signings on every support in `F`. -/
def fullSigningFamily (F : Finset (Support4 ι)) : Finset (SignedSupport ι) :=
  (F.sigma signingChoices).map signedChoiceEmbedding

lemma card_signingChoices (S : Support4 ι) : (signingChoices S).card = 16 := by
  simp [signingChoices, S.card_eq]

lemma card_fullSigningFamily (F : Finset (Support4 ι)) :
    (fullSigningFamily F).card = 16 * F.card := by
  classical
  rw [fullSigningFamily, Finset.card_map, Finset.card_sigma]
  simp [card_signingChoices, mul_comm]

lemma full_signing_family_compatible {F : Finset (Support4 ι)}
    (hF : SupportCompatible F) : SignedCompatible (fullSigningFamily F) := by
  classical
  intro r hr s hs hrs _hsigns
  rw [fullSigningFamily, Finset.mem_map] at hr hs
  obtain ⟨p, hp, rfl⟩ := hr
  obtain ⟨q, hq, rfl⟩ := hs
  have hpF : p.1 ∈ F := (Finset.mem_sigma.mp hp).1
  have hqF : q.1 ∈ F := (Finset.mem_sigma.mp hq).1
  exact hF p.1 hpF q.1 hqF hrs

/-- **Signed-shell identity.** For `n ≥ 4`, the signed independence
number is exactly sixteen times the four-support packing number:
`α(J_±(n,4)) = 16 A(n,4,4)`. -/
theorem signed_shell_identity [Fintype ι] (A : ℕ) (hn : 4 ≤ Fintype.card ι)
    (hA : IsSupportMaximum (ι := ι) A) :
    IsSignedMaximum (ι := ι) (16 * A) := by
  constructor
  · intro C hC
    exact signed_shell_upper A hn hA.1 C hC
  · obtain ⟨F, hF, hcard⟩ := hA.2
    refine ⟨fullSigningFamily F, full_signing_family_compatible hF, ?_⟩
    rw [card_fullSigningFamily, hcard]

def degree (F : Finset (Support4 ι)) (x : ι) : ℕ :=
  (F.filter (fun S => x ∈ S.carrier)).card

lemma sum_degrees [Fintype ι] (F : Finset (Support4 ι)) :
    (∑ x : ι, degree F x) = 4 * F.card := by
  classical
  calc
    (∑ x : ι, degree F x) =
        ∑ x : ι, ∑ S ∈ F, if x ∈ S.carrier then 1 else 0 := by
          simp only [degree, Finset.card_filter]
    _ = ∑ S ∈ F, ∑ x : ι, if x ∈ S.carrier then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ _S ∈ F, 4 := by
      apply Finset.sum_congr rfl
      intro S hS
      simp [S.card_eq]
    _ = 4 * F.card := by simp [mul_comm]

lemma sum_degrees_on (F : Finset (Support4 ι)) (R : Finset ι) :
    (∑ x ∈ R, degree F x) = ∑ S ∈ F, (S.carrier ∩ R).card := by
  classical
  calc
    (∑ x ∈ R, degree F x) =
        ∑ x ∈ R, ∑ S ∈ F, if x ∈ S.carrier then 1 else 0 := by
          simp only [degree, Finset.card_filter]
    _ = ∑ S ∈ F, ∑ x ∈ R, if x ∈ S.carrier then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ S ∈ F, (S.carrier ∩ R).card := by
      apply Finset.sum_congr rfl
      intro S hS
      simp [Finset.inter_comm]

def codegree (F : Finset (Support4 ι)) (x y : ι) : ℕ :=
  (F.filter (fun S => x ∈ S.carrier ∧ y ∈ S.carrier)).card

lemma degree_codegree_family (F : Finset (Support4 ι)) (x y z : ι) :
    degree (F.filter (fun S => x ∈ S.carrier ∧ y ∈ S.carrier)) z =
      (F.filter (fun S => x ∈ S.carrier ∧ y ∈ S.carrier ∧ z ∈ S.carrier)).card := by
  classical
  simp only [degree, Finset.filter_filter]
  congr 1
  ext S
  simp only [Finset.mem_filter]
  tauto

lemma triple_codegree_le_one {F : Finset (Support4 ι)} (hF : SupportCompatible F)
    {x y z : ι} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (F.filter (fun S => x ∈ S.carrier ∧ y ∈ S.carrier ∧ z ∈ S.carrier)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro S hS T hT
  simp only [Finset.mem_filter] at hS hT
  by_contra hST
  have hle := hF S hS.1 T hT.1 hST
  have hsub : ({x, y, z} : Finset ι) ⊆ S.carrier ∩ T.carrier := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rw [Finset.mem_inter]
    rcases hw with rfl | rfl | rfl
    · exact ⟨hS.2.1, hT.2.1⟩
    · exact ⟨hS.2.2.1, hT.2.2.1⟩
    · exact ⟨hS.2.2.2, hT.2.2.2⟩
  have hthree : ({x, y, z} : Finset ι).card = 3 := by
    simp [hxy, hxz, hyz]
  have := Finset.card_le_card hsub
  omega

lemma codegree_le_four_fin11 {F : Finset (Support4 (Fin 11))}
    (hF : SupportCompatible F) {x y : Fin 11} (hxy : x ≠ y) :
    codegree F x y ≤ 4 := by
  classical
  let H := F.filter (fun S => x ∈ S.carrier ∧ y ∈ S.carrier)
  let R := Finset.univ \ {x, y}
  have hRcard : R.card = 9 := by
    rw [show R = Finset.univ \ {x, y} by rfl, Finset.card_sdiff,
      Finset.inter_eq_left.mpr (Finset.subset_univ _)]
    simp [hxy]
  have hlocal : ∀ z ∈ R, degree H z ≤ 1 := by
    intro z hz
    have hzx : z ≠ x := by
      intro h
      subst z
      exact (Finset.mem_sdiff.mp hz).2 (by simp)
    have hzy : z ≠ y := by
      intro h
      subst z
      exact (Finset.mem_sdiff.mp hz).2 (by simp)
    rw [degree_codegree_family]
    exact triple_codegree_le_one hF hxy hzx.symm hzy.symm
  have hintersection : ∀ S ∈ H, (S.carrier ∩ R).card = 2 := by
    intro S hS
    have hmem : x ∈ S.carrier ∧ y ∈ S.carrier := (Finset.mem_filter.mp hS).2
    have hpair : ({x, y} : Finset (Fin 11)) ⊆ S.carrier := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hmem.1
      · exact hmem.2
    have heq : S.carrier ∩ R = S.carrier \ {x, y} := by
      ext z
      simp [R]
    rw [heq, Finset.card_sdiff, Finset.inter_eq_left.mpr hpair, S.card_eq]
    simp [hxy]
  have hincidence : 2 * H.card ≤ 9 := by
    calc
      2 * H.card = ∑ S ∈ H, (S.carrier ∩ R).card := by
        rw [show (∑ S ∈ H, (S.carrier ∩ R).card) = ∑ _S ∈ H, 2 by
          apply Finset.sum_congr rfl
          exact hintersection]
        simp [mul_comm]
      _ = ∑ z ∈ R, degree H z := (sum_degrees_on H R).symm
      _ ≤ ∑ _z ∈ R, 1 := Finset.sum_le_sum hlocal
      _ = 9 := by simp [hRcard]
  change H.card ≤ 4
  omega

lemma degree_le_thirteen_fin11 {F : Finset (Support4 (Fin 11))}
    (hF : SupportCompatible F) (x : Fin 11) : degree F x ≤ 13 := by
  classical
  let H := F.filter (fun S => x ∈ S.carrier)
  let R := Finset.univ.erase x
  have hRcard : R.card = 10 := by simp [R]
  have hlocal : ∀ y ∈ R, degree H y ≤ 4 := by
    intro y hy
    have hxy : x ≠ y := by
      intro h
      subst y
      exact (Finset.mem_erase.mp hy).1 rfl
    have heq : degree H y = codegree F x y := by
      simp only [degree, codegree, H, Finset.filter_filter]
    rw [heq]
    exact codegree_le_four_fin11 hF hxy
  have hintersection : ∀ S ∈ H, (S.carrier ∩ R).card = 3 := by
    intro S hS
    have hxS : x ∈ S.carrier := (Finset.mem_filter.mp hS).2
    have heq : S.carrier ∩ R = S.carrier.erase x := by
      ext z
      simp [R, and_comm]
    rw [heq, Finset.card_erase_of_mem hxS, S.card_eq]
  have hincidence : 3 * H.card ≤ 40 := by
    calc
      3 * H.card = ∑ S ∈ H, (S.carrier ∩ R).card := by
        rw [show (∑ S ∈ H, (S.carrier ∩ R).card) = ∑ _S ∈ H, 3 by
          apply Finset.sum_congr rfl
          exact hintersection]
        simp [mul_comm]
      _ = ∑ y ∈ R, degree H y := (sum_degrees_on H R).symm
      _ ≤ ∑ _y ∈ R, 4 := Finset.sum_le_sum hlocal
      _ = 40 := by simp [hRcard]
  change H.card ≤ 13
  omega

/-- The elementary nested incidence bound used in the Station archive:
every 4-uniform 3-packing on eleven points has at most 35 blocks. -/
theorem support_upper_fin11 (F : Finset (Support4 (Fin 11)))
    (hF : SupportCompatible F) : F.card ≤ 35 := by
  have hsum := sum_degrees F
  have hdeg : (∑ x : Fin 11, degree F x) ≤ ∑ _x : Fin 11, 13 := by
    exact Finset.sum_le_sum fun x _hx => degree_le_thirteen_fin11 hF x
  rw [hsum] at hdeg
  norm_num at hdeg
  omega

def support4Embedding :
    {S : Finset (Fin 11) // S ∈ Finset.univ.powersetCard 4} ↪ Support4 (Fin 11) where
  toFun S := ⟨S.1, (Finset.mem_powersetCard.mp S.2).2⟩
  inj' := by
    intro S T h
    apply Subtype.ext
    exact congrArg Support4.carrier h

def allSupports4Fin11 : Finset (Support4 (Fin 11)) :=
  Finset.univ.powersetCard 4 |>.attach.map support4Embedding

/-- The explicit 35-block packing recorded in the Station archive (zero-based
coordinates). -/
def witnessCarriers : Finset (Finset (Fin 11)) :=
  [
    {0,1,2,6}, {0,1,3,9}, {0,1,8,10}, {0,2,3,7}, {0,2,4,10},
    {0,2,5,8}, {0,3,4,6}, {0,3,5,10}, {0,4,5,7}, {0,4,8,9},
    {0,5,6,9}, {0,6,7,8}, {0,7,9,10}, {1,2,3,8}, {1,2,4,9},
    {1,2,5,10}, {1,3,4,10}, {1,3,5,7}, {1,4,6,7}, {1,5,6,8},
    {1,6,9,10}, {1,7,8,9}, {2,3,5,9}, {2,3,6,10}, {2,4,5,6},
    {2,4,7,8}, {2,6,7,9}, {2,8,9,10}, {3,4,5,8}, {3,4,7,9},
    {3,6,8,9}, {3,7,8,10}, {4,5,9,10}, {4,6,8,10}, {5,6,7,10}
  ].toFinset

def supportWitnessFin11 : Finset (Support4 (Fin 11)) :=
  allSupports4Fin11.filter (fun S => S.carrier ∈ witnessCarriers)

lemma support_witness_card : supportWitnessFin11.card = 35 := by
  decide

lemma support_witness_compatible : SupportCompatible supportWitnessFin11 := by
  decide

/-- The exact constant-weight packing value `A(11,4,4) = 35`, proved by
the incidence upper bound and an explicit attaining family. -/
theorem support_maximum_fin11 :
    IsSupportMaximum (ι := Fin 11) 35 := by
  refine ⟨support_upper_fin11, supportWitnessFin11, support_witness_compatible, ?_⟩
  exact support_witness_card

/-- The dimension-eleven instance of the signed-shell identity:
the signed weight-four part has exact maximum `16 * 35 = 560`. -/
theorem signed_weight_four_maximum_fin11 :
    IsSignedMaximum (ι := Fin 11) 560 := by
  simpa only [Nat.reduceMul] using
    signed_shell_identity (ι := Fin 11) 35 (by decide) support_maximum_fin11

/-- The canonical classification of the complete norm-four `D₁₁` shell:
an axis row `±2eᵢ`, or a signed row with four `±1` entries. -/
abbrev D11ShellPoint := (Fin 11 × Bool) ⊕ SignedSupport (Fin 11)

def boolSign (b : Bool) : ℤ := if b then -1 else 1

/-- The actual integer vector represented by a canonical shell point. -/
def D11ShellPoint.vector : D11ShellPoint → (Fin 11 → ℤ)
  | Sum.inl a => fun j => if j = a.1 then 2 * boolSign a.2 else 0
  | Sum.inr r => fun j =>
      if j ∈ r.support.carrier then if j ∈ r.negative then -1 else 1 else 0

/-- Actual Euclidean dot product of the represented integer vectors. -/
def D11ShellPoint.inner (p q : D11ShellPoint) : ℤ :=
  ∑ i : Fin 11, p.vector i * q.vector i

/-- The canonical representation has no duplicate vectors. -/
theorem shell_vector_injective : Function.Injective D11ShellPoint.vector := by
  intro p q hvec
  cases p with
  | inl a =>
    cases q with
    | inl b =>
      have hv := congrFun hvec a.1
      have hcoord : a.1 = b.1 := by
        by_contra hne
        cases ha : a.2 <;> simp [D11ShellPoint.vector, hne, boolSign, ha] at hv
      have hsign : a.2 = b.2 := by
        cases ha : a.2 <;> cases hb : b.2 <;>
          simp [D11ShellPoint.vector, hcoord, boolSign, ha, hb] at hv ⊢
      exact congrArg Sum.inl (Prod.ext hcoord hsign)
    | inr r =>
      exfalso
      have hex : ∃ i ∈ r.support.carrier, i ≠ a.1 := by
        by_contra h
        push_neg at h
        have hsub : r.support.carrier ⊆ {a.1} := by
          intro i hi
          simp [h i hi]
        have hc := Finset.card_le_card hsub
        rw [r.support.card_eq] at hc
        simp at hc
      obtain ⟨i, hi, hia⟩ := hex
      have hv := congrFun hvec i
      by_cases hin : i ∈ r.negative <;>
        simp [D11ShellPoint.vector, hi, hia, hin] at hv
  | inr r =>
    cases q with
    | inl a =>
      exfalso
      have hex : ∃ i ∈ r.support.carrier, i ≠ a.1 := by
        by_contra h
        push_neg at h
        have hsub : r.support.carrier ⊆ {a.1} := by
          intro i hi
          simp [h i hi]
        have hc := Finset.card_le_card hsub
        rw [r.support.card_eq] at hc
        simp at hc
      obtain ⟨i, hi, hia⟩ := hex
      have hv := congrFun hvec i
      by_cases hin : i ∈ r.negative <;>
        simp [D11ShellPoint.vector, hi, hia, hin] at hv
    | inr s =>
      have hcarrier : r.support.carrier = s.support.carrier := by
        apply Finset.ext
        intro i
        have hv := congrFun hvec i
        by_cases hir : i ∈ r.support.carrier <;>
          by_cases his : i ∈ s.support.carrier <;>
          by_cases hinr : i ∈ r.negative <;>
          by_cases hins : i ∈ s.negative <;>
          simp_all [D11ShellPoint.vector]
      have hsupport : r.support = s.support :=
        Support4.extensionality _ _ hcarrier
      have hnegative : r.negative = s.negative := by
        apply Finset.ext
        intro i
        have hv := congrFun hvec i
        by_cases hir : i ∈ r.support.carrier
        · have his : i ∈ s.support.carrier := by simpa [← hcarrier]
          by_cases hinr : i ∈ r.negative <;>
            by_cases hins : i ∈ s.negative <;>
            simp_all [D11ShellPoint.vector]
        · have hinr : i ∉ r.negative := fun hi => hir (r.negative_subset hi)
          have his : i ∉ s.support.carrier := by simpa [← hcarrier]
          have hins : i ∉ s.negative := fun hi => his (s.negative_subset hi)
          simp [hinr, hins]
      cases r
      cases s
      simp_all

lemma inner_signed_signed (r s : SignedSupport (Fin 11)) :
    D11ShellPoint.inner (Sum.inr r) (Sum.inr s) = signedInnerProduct r s := by
  classical
  unfold D11ShellPoint.inner
  rw [show (∑ i : Fin 11, D11ShellPoint.vector (Sum.inr r) i *
      D11ShellPoint.vector (Sum.inr s) i) =
      ∑ i : Fin 11, if i ∈ signAgreements r s then (1 : ℤ)
        else if i ∈ signDisagreements r s then -1 else 0 by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hir : i ∈ r.support.carrier <;>
      by_cases his : i ∈ s.support.carrier <;>
      by_cases hinr : i ∈ r.negative <;>
      by_cases hins : i ∈ s.negative <;>
      simp_all [D11ShellPoint.vector, signAgreements, signDisagreements, commonSupport]]
  rw [show (∑ i : Fin 11, if i ∈ signAgreements r s then (1 : ℤ)
      else if i ∈ signDisagreements r s then -1 else 0) =
      (∑ i : Fin 11, if i ∈ signAgreements r s then (1 : ℤ) else 0) -
      ∑ i : Fin 11, if i ∈ signDisagreements r s then (1 : ℤ) else 0 by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases ha : i ∈ signAgreements r s <;>
      by_cases hd : i ∈ signDisagreements r s <;>
      simp_all [signAgreements, signDisagreements]]
  simp [signedInnerProduct]

lemma inner_axis_axis (a b : Fin 11 × Bool) :
    D11ShellPoint.inner (Sum.inl a) (Sum.inl b) =
      if a.1 = b.1 then 4 * boolSign a.2 * boolSign b.2 else 0 := by
  classical
  unfold D11ShellPoint.inner
  rw [Finset.sum_eq_single a.1]
  · by_cases h : a.1 = b.1
    · simp [D11ShellPoint.vector, h]
      ring
    · simp [D11ShellPoint.vector, h]
  · intro j hj hja
    simp [D11ShellPoint.vector, hja]
  · simp

lemma inner_axis_signed (a : Fin 11 × Bool) (r : SignedSupport (Fin 11)) :
    D11ShellPoint.inner (Sum.inl a) (Sum.inr r) =
      if a.1 ∈ r.support.carrier then
        2 * boolSign a.2 * (if a.1 ∈ r.negative then -1 else 1)
      else 0 := by
  classical
  unfold D11ShellPoint.inner
  rw [Finset.sum_eq_single a.1]
  · simp [D11ShellPoint.vector]
  · intro j hj hja
    simp [D11ShellPoint.vector, hja]
  · simp

lemma inner_signed_axis (r : SignedSupport (Fin 11)) (a : Fin 11 × Bool) :
    D11ShellPoint.inner (Sum.inr r) (Sum.inl a) =
      D11ShellPoint.inner (Sum.inl a) (Sum.inr r) := by
  unfold D11ShellPoint.inner
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Pairwise kissing compatibility, now stated using the literal dot product of
the integer vectors above. -/
def D11ShellCompatible (C : Finset D11ShellPoint) : Prop :=
  ∀ p ∈ C, ∀ q ∈ C, p ≠ q → D11ShellPoint.inner p q ≤ 2

instance (C : Finset D11ShellPoint) : Decidable (D11ShellCompatible C) := by
  unfold D11ShellCompatible
  infer_instance

def shellSignedOption : D11ShellPoint → Option (SignedSupport (Fin 11))
  | Sum.inl _ => none
  | Sum.inr r => some r

lemma shellSignedOption_injective :
    ∀ p q r, r ∈ shellSignedOption p → r ∈ shellSignedOption q → p = q := by
  intro p q r hp hq
  cases p <;> cases q <;> simp_all [shellSignedOption]

def shellSignedRows (C : Finset D11ShellPoint) : Finset (SignedSupport (Fin 11)) :=
  C.filterMap shellSignedOption shellSignedOption_injective

@[simp] lemma mem_shellSignedRows {C : Finset D11ShellPoint}
    {r : SignedSupport (Fin 11)} : r ∈ shellSignedRows C ↔ Sum.inr r ∈ C := by
  simp [shellSignedRows, shellSignedOption]

def isAxisPoint : D11ShellPoint → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

instance : DecidablePred isAxisPoint := fun p => match p with
  | Sum.inl _ => isTrue trivial
  | Sum.inr _ => isFalse id

def shellAxisOption : D11ShellPoint → Option (Fin 11 × Bool)
  | Sum.inl a => some a
  | Sum.inr _ => none

lemma shellAxisOption_injective :
    ∀ p q a, a ∈ shellAxisOption p → a ∈ shellAxisOption q → p = q := by
  intro p q a hp hq
  cases p <;> cases q <;> simp_all [shellAxisOption]

def shellAxisRows (C : Finset D11ShellPoint) : Finset (Fin 11 × Bool) :=
  C.filterMap shellAxisOption shellAxisOption_injective

@[simp] lemma mem_shellAxisRows {C : Finset D11ShellPoint} {a : Fin 11 × Bool} :
    a ∈ shellAxisRows C ↔ Sum.inl a ∈ C := by
  simp [shellAxisRows, shellAxisOption]

lemma card_signed_filter (C : Finset D11ShellPoint) :
    (C.filter (fun p => ¬ isAxisPoint p)).card = (shellSignedRows C).card := by
  classical
  apply Finset.card_bij
    (fun p hp => match p with
      | Sum.inl a => False.elim (by simpa [isAxisPoint] using (Finset.mem_filter.mp hp).2)
      | Sum.inr r => r)
  · intro p hp
    cases p with
    | inl a => simp [isAxisPoint] at hp
    | inr r => simpa using (Finset.mem_filter.mp hp).1
  · intro p hp q hq heq
    cases p with
    | inl a => simp [isAxisPoint] at hp
    | inr r =>
      cases q with
      | inl a => simp [isAxisPoint] at hq
      | inr s => simpa using heq
  · intro r hr
    refine ⟨Sum.inr r, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨mem_shellSignedRows.mp hr, by simp [isAxisPoint]⟩

lemma card_axis_filter_le (C : Finset D11ShellPoint) :
    (C.filter isAxisPoint).card ≤ 22 := by
  classical
  have hcardeq : (C.filter isAxisPoint).card = (shellAxisRows C).card := by
    apply Finset.card_bij
      (fun p hp => match p with
        | Sum.inl a => a
        | Sum.inr r => False.elim (by
            simpa [isAxisPoint] using (Finset.mem_filter.mp hp).2))
    · intro p hp
      cases p with
      | inl a => simpa using (Finset.mem_filter.mp hp).1
      | inr r => simp [isAxisPoint] at hp
    · intro p hp q hq heq
      cases p with
      | inl a =>
        cases q with
        | inl b => simpa using heq
        | inr s => simp [isAxisPoint] at hq
      | inr r => simp [isAxisPoint] at hp
    · intro a ha
      exact ⟨Sum.inl a, Finset.mem_filter.mpr ⟨mem_shellAxisRows.mp ha,
        by simp [isAxisPoint]⟩, rfl⟩
  rw [hcardeq]
  calc
    (shellAxisRows C).card ≤ Fintype.card (Fin 11 × Bool) := Finset.card_le_univ _
    _ = 22 := by decide

lemma shell_signed_rows_compatible {C : Finset D11ShellPoint}
    (hC : D11ShellCompatible C) : SignedCompatible (shellSignedRows C) := by
  rw [signed_compatible_iff_inner_product]
  intro r hr s hs hrs
  rw [← inner_signed_signed]
  exact hC (Sum.inr r) (mem_shellSignedRows.mp hr)
    (Sum.inr s) (mem_shellSignedRows.mp hs) (by simpa)

def axisShellPoints : Finset D11ShellPoint :=
  (Finset.univ : Finset (Fin 11 × Bool)).map
    ⟨Sum.inl, fun _ _ h => Sum.inl.inj h⟩

def signedShellPoints (W : Finset (SignedSupport (Fin 11))) : Finset D11ShellPoint :=
  W.map ⟨Sum.inr, fun _ _ h => Sum.inr.inj h⟩

@[simp] lemma mem_axisShellPoints (a : Fin 11 × Bool) :
    Sum.inl a ∈ axisShellPoints := by simp [axisShellPoints]

@[simp] lemma mem_signedShellPoints {W : Finset (SignedSupport (Fin 11))}
    {r : SignedSupport (Fin 11)} : Sum.inr r ∈ signedShellPoints W ↔ r ∈ W := by
  simp [signedShellPoints]

lemma axis_shell_points_card : axisShellPoints.card = 22 := by decide

lemma signed_shell_points_card (W : Finset (SignedSupport (Fin 11))) :
    (signedShellPoints W).card = W.card := by simp [signedShellPoints]

lemma axis_signed_shell_disjoint (W : Finset (SignedSupport (Fin 11))) :
    Disjoint axisShellPoints (signedShellPoints W) := by
  rw [Finset.disjoint_left]
  intro p hpaxis hpsigned
  obtain ⟨a, ha, hap⟩ := Finset.mem_map.mp hpaxis
  obtain ⟨r, hr, hrp⟩ := Finset.mem_map.mp hpsigned
  subst p
  cases hrp

lemma complete_shell_witness_compatible {W : Finset (SignedSupport (Fin 11))}
    (hW : SignedCompatible W) :
    D11ShellCompatible (axisShellPoints ∪ signedShellPoints W) := by
  intro p hp q hq hpq
  rw [Finset.mem_union] at hp hq
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hq
    change D11ShellPoint.inner (Sum.inl a) (Sum.inl b) ≤ 2
    change (Sum.inl a : D11ShellPoint) ≠ Sum.inl b at hpq
    rw [inner_axis_axis]
    by_cases hi : a.1 = b.1
    · simp only [hi, ↓reduceIte]
      have hb : a.2 ≠ b.2 := by
        intro hab
        apply hpq
        exact congrArg Sum.inl (Prod.ext hi hab)
      cases ha : a.2 <;> cases hb' : b.2 <;> simp_all [boolSign]
    · simp [hi]
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hp
    obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp hq
    change D11ShellPoint.inner (Sum.inl a) (Sum.inr r) ≤ 2
    rw [inner_axis_signed]
    by_cases hsupp : a.1 ∈ r.support.carrier <;>
      by_cases hneg : a.1 ∈ r.negative <;>
      cases a.2 <;> simp [hsupp, hneg, boolSign]
  · obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hq
    change D11ShellPoint.inner (Sum.inr r) (Sum.inl a) ≤ 2
    rw [inner_signed_axis, inner_axis_signed]
    by_cases hsupp : a.1 ∈ r.support.carrier <;>
      by_cases hneg : a.1 ∈ r.negative <;>
      cases a.2 <;> simp [hsupp, hneg, boolSign]
  · obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp hp
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hq
    change D11ShellPoint.inner (Sum.inr r) (Sum.inr s) ≤ 2
    change (Sum.inr r : D11ShellPoint) ≠ Sum.inr s at hpq
    rw [inner_signed_signed]
    exact (signed_compatible_iff_inner_product W).mp hW r hr s hs (by simpa using hpq)

def IsD11ShellMaximum (M : ℕ) : Prop :=
  (∀ C : Finset D11ShellPoint, D11ShellCompatible C → C.card ≤ M) ∧
  ∃ C : Finset D11ShellPoint, D11ShellCompatible C ∧ C.card = M

/-- **Spotlight 3, dimension-eleven corollary.** For the actual integer-vector
dot product, the exact maximum compatible subset of the complete norm-four
`D₁₁` shell is `22 + 560 = 582`. This is a shell-specific result, not an upper
bound for the full kissing number `K(11)`. -/
theorem d11_norm_four_shell_maximum : IsD11ShellMaximum 582 := by
  constructor
  · intro C hC
    have hpartition := Finset.filter_card_add_filter_neg_card_eq_card
      (s := C) isAxisPoint
    have haxis := card_axis_filter_le C
    have hsigned : (shellSignedRows C).card ≤ 560 :=
      signed_weight_four_maximum_fin11.1 _ (shell_signed_rows_compatible hC)
    rw [card_signed_filter] at hpartition
    omega
  · obtain ⟨W, hW, hWcard⟩ := signed_weight_four_maximum_fin11.2
    refine ⟨axisShellPoints ∪ signedShellPoints W,
      complete_shell_witness_compatible hW, ?_⟩
    rw [Finset.card_union_of_disjoint (axis_signed_shell_disjoint W),
      axis_shell_points_card, signed_shell_points_card, hWcard]

end KissingS3
