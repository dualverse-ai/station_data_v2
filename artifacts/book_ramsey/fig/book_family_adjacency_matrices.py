#!/usr/bin/env python3
"""Render block-ordered adjacency matrices for the three book families."""

from __future__ import annotations

import hashlib
import json
import os
import tempfile
from pathlib import Path

os.environ.setdefault("MPLCONFIGDIR", os.path.join(tempfile.gettempdir(), "book_ramsey_mplconfig"))

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import BoundaryNorm, ListedColormap
from matplotlib.lines import Line2D
import numpy as np
from PIL import Image


HERE = Path(__file__).resolve().parent
OUT = HERE
OUT.mkdir(parents=True, exist_ok=True)

INK = "#22262A"
MID_INK = "#62686D"
RED = "#B6534D"
BLUE = "#376DBA"
WHITE = "#FFFFFF"
SEPARATOR = "#F5F5F3"


# Upper-triangular adjacency strings, read column by column.  These are the
# exact verified examples shown in the figure, extracted from the accompanying
# construction notebooks.
GRAPH_CERTIFICATES = [
    {
        "key": "S1",
        "name": "Conference family",
        "n": 6,
        "sha256": "84ce382953bf24a148b0476e5b3179f373c7276b56768257c454df80f5e5dd90",
        "bits": """
            101001100110110010110101011011010110011010110110010011011100000110011101000110001111100011
            010011011000110001100011001001000110001110100110001100010101001110001100000101001011000110
            010010100100000000001111111111000001111100000111110
        """,
    },
    {
        "key": "S2",
        "name": "Doubled Legendre family",
        "n": 6,
        "sha256": "29f0688397a1d4ac8f1453b7b172a6eaad529236293fe6e55ea97ce3852e98a3",
        "bits": """
            010110011000011100011110000101100001001101001101100110001011001101101010001101110101000100
            101101110001001000110100111100100011010001110011000010100011110011000010110011110001101001
            011001011000000111110000011111111111111100000000000
        """,
    },
    {
        "key": "S3",
        "name": "Yamada–Pott family",
        "n": 11,
        "sha256": "22c2a5e7bb2ebee5b112a38f2b64f56a34a16eedca1542826a0985b855492506",
        "bits": """
            010010001000010000010100001011000010011000010101100001011011000010011011000010101101100001
            011011011000010011011011000010001101101100001000011011011000010000011011011000010100001101
            101100001001000011011011000010010100001101110011111101010000110111001111111010100001101110
            011101111010100001101110011001111101010000110111001100111111010100001101110011001011111010
            100001101110011001001111101010000110111101100110011111010100001101101011001110011111010100
            001101001011001111001111101010000110000101100101110011111010100001100001011001101110011111
            010100001000001011001110111001111101010000000000101100101101110011111010100010000001011001
            001101110011111010100010000001011001000110111001111101010101000000101100100001101110011111
            010111010000001011001100001101110011111010011010000001011001010000110111001111101001101000
            000101100110100001101110011111010011010000001011001
        """,
    },
]


def masks_from_adjacency_string(bits: str, vertex_count: int) -> tuple[int, ...]:
    bits = "".join(bits.split())
    expected = vertex_count * (vertex_count - 1) // 2
    if len(bits) != expected:
        raise ValueError(f"certificate has {len(bits)} bits, expected {expected}")
    masks = [0] * vertex_count
    cursor = 0
    for j in range(1, vertex_count):
        for i in range(j):
            if bits[cursor] == "1":
                masks[i] |= 1 << j
                masks[j] |= 1 << i
            cursor += 1
    return tuple(masks)


def audit_book_coloring(masks: tuple[int, ...], n: int) -> dict[str, int | bool]:
    """Check that red avoids B_(n-1) and blue avoids B_n."""
    vertex_count = 4 * n - 2
    if len(masks) != vertex_count:
        raise ValueError(f"got {len(masks)} vertices, expected {vertex_count}")
    universe = (1 << vertex_count) - 1
    complement = tuple(universe ^ (1 << i) ^ masks[i] for i in range(vertex_count))
    red_max = blue_max = -1
    red_edges = 0
    for j in range(1, vertex_count):
        for i in range(j):
            if (masks[j] >> i) & 1:
                red_edges += 1
                red_max = max(red_max, (masks[i] & masks[j]).bit_count())
            else:
                blue_max = max(blue_max, (complement[i] & complement[j]).bit_count())
    return {
        "vertices": vertex_count,
        "red_edges": red_edges,
        "blue_edges": vertex_count * (vertex_count - 1) // 2 - red_edges,
        "max_red_pages": red_max,
        "max_blue_pages": blue_max,
        "valid": red_max <= n - 2 and blue_max <= n - 1,
    }


def load_small_graphs() -> list[dict[str, object]]:
    graphs = []
    for certificate in GRAPH_CERTIFICATES:
        bits = "".join(certificate["bits"].split())
        if hashlib.sha256(bits.encode()).hexdigest() != certificate["sha256"]:
            raise ValueError(f"checksum mismatch for {certificate['key']}")
        masks = masks_from_adjacency_string(bits, 4 * certificate["n"] - 2)
        audit = audit_book_coloring(masks, certificate["n"])
        if not audit["valid"]:
            raise AssertionError(f"invalid book coloring for {certificate['key']}: {audit}")
        graph = dict(certificate)
        graph["masks"] = masks
        graph["audit"] = audit
        graphs.append(graph)
        print(certificate["key"], audit)
    return graphs


def adjacency_image(masks: tuple[int, ...]) -> np.ndarray:
    order = len(masks)
    image = np.zeros((order, order), dtype=np.uint8)
    for i in range(order):
        for j in range(order):
            if i == j:
                image[i, j] = 2
            elif (masks[i] >> j) & 1:
                image[i, j] = 1
    return image


def group_metadata(graph: dict[str, object]) -> tuple[list[int], list[str]]:
    if graph["key"] == "S1":
        sizes = [5, 5, 5, 5, 1, 1]
        labels = [r"$BB$", r"$BR$", r"$RB$", r"$RR$", r"$u$", r"$v$"]
    elif graph["key"] == "S2":
        sizes = [5, 5, 5, 5, 1, 1]
        labels = [r"$0{+}$", r"$0{-}$", r"$1{+}$", r"$1{-}$", r"$u$", r"$v$"]
    else:
        sizes = [21, 21]
        labels = [r"$F_1$", r"$F_2$"]
    assert sum(sizes) == len(graph["masks"])
    return sizes, labels


def draw_matrix(ax: plt.Axes, graph: dict[str, object]) -> None:
    matrix = adjacency_image(graph["masks"])
    order = matrix.shape[0]
    cmap = ListedColormap([BLUE, RED, WHITE])
    norm = BoundaryNorm([-0.5, 0.5, 1.5, 2.5], cmap.N)
    ax.imshow(matrix, cmap=cmap, norm=norm, interpolation="nearest", origin="upper")

    sizes, labels = group_metadata(graph)
    starts = np.cumsum([0] + sizes[:-1]).tolist()
    centers = [start + (size - 1) / 2 for start, size in zip(starts, sizes)]

    boundaries = np.cumsum(sizes)[:-1]
    for boundary in boundaries:
        ax.axhline(boundary - 0.5, color=SEPARATOR, linewidth=1.15, zorder=4)
        ax.axvline(boundary - 0.5, color=SEPARATOR, linewidth=1.15, zorder=4)

    ax.set_xticks(centers, labels)
    ax.set_yticks(centers, labels)
    ax.xaxis.tick_top()
    ax.tick_params(axis="x", length=0, pad=4.0, labelsize=7.1, colors=INK)
    ax.tick_params(axis="y", length=0, pad=3.0, labelsize=7.1, colors=INK)
    ax.set_xlim(-0.5, order - 0.5)
    ax.set_ylim(order - 0.5, -0.5)
    ax.set_aspect("equal")
    for spine in ax.spines.values():
        spine.set_color(INK)
        spine.set_linewidth(0.62)


def nonwhite_bounds(image: np.ndarray, threshold: int = 249) -> tuple[int, int, int, int]:
    mask = np.any(image[:, :, :3] < threshold, axis=2)
    ys, xs = np.where(mask)
    return int(xs.min()), int(ys.min()), int(xs.max()), int(ys.max())


def main() -> None:
    graphs = load_small_graphs()
    plt.rcParams.update(
        {
            "font.family": "sans-serif",
            "font.sans-serif": ["DejaVu Sans"],
            "mathtext.fontset": "dejavusans",
            "figure.facecolor": "white",
            "savefig.facecolor": "white",
            "pdf.fonttype": 42,
            "ps.fonttype": 42,
        }
    )

    fig = plt.figure(figsize=(7.45, 3.75), dpi=300)
    grid = fig.add_gridspec(
        1,
        3,
        left=0.035,
        right=0.992,
        top=0.860,
        bottom=0.255,
        wspace=0.110,
    )
    axes = [fig.add_subplot(grid[0, column]) for column in range(3)]
    for ax, graph in zip(axes, graphs):
        draw_matrix(ax, graph)

    details = [
        (
            r"Conference family ($n=6$)",
            r"4 chambers: $BB,BR,RB,RR$",
            r"5 vertices each; endpoints: $u,v$",
        ),
        (
            r"Doubled Legendre family ($n=6$)",
            r"4 layers: $0{+},0{-},1{+},1{-}$",
            r"5 vertices each; endpoints: $u,v$",
        ),
        (
            r"Yamada–Pott family ($n=11$)",
            r"2 affine fibres: $F_1,F_2$",
            r"21 vertices each",
        ),
    ]
    for index, (ax, (name, structure, size_detail)) in enumerate(zip(axes, details)):
        box = ax.get_position()
        fig.text(
            (box.x0 + box.x1) / 2,
            0.202,
            f"({chr(97 + index)}) {name}",
            ha="center",
            va="center",
            fontsize=8.6,
            fontweight="bold",
            color=INK,
        )
        fig.text(
            (box.x0 + box.x1) / 2,
            0.157,
            structure,
            ha="center",
            va="center",
            fontsize=7.0,
            color=INK,
        )
        fig.text(
            (box.x0 + box.x1) / 2,
            0.123,
            size_detail,
            ha="center",
            va="center",
            fontsize=7.0,
            color=INK,
        )

    handles = [
        Line2D([0], [0], marker="s", linestyle="none", markerfacecolor=RED, markeredgecolor="none", markersize=6, label="red edge"),
        Line2D([0], [0], marker="s", linestyle="none", markerfacecolor=BLUE, markeredgecolor="none", markersize=6, label="blue edge"),
        Line2D([0], [0], marker="s", linestyle="none", markerfacecolor=WHITE, markeredgecolor="#B8BCC0", markeredgewidth=0.7, markersize=6, label="diagonal (no edge)"),
    ]
    fig.legend(
        handles=handles,
        loc="lower center",
        bbox_to_anchor=(0.5, 0.030),
        ncol=3,
        frameon=False,
        columnspacing=1.45,
        handletextpad=0.42,
        fontsize=7.1,
        labelcolor=MID_INK,
    )

    stem = OUT / "book_family_adjacency_matrices"
    fig.savefig(stem.with_suffix(".png"), dpi=300, bbox_inches="tight", pad_inches=0.025)
    fig.savefig(stem.with_suffix(".pdf"), bbox_inches="tight", pad_inches=0.025)
    fig.canvas.draw()

    saved = np.asarray(Image.open(stem.with_suffix(".png")).convert("RGB"))
    saved_h, saved_w = saved.shape[:2]
    matrix_boxes = []
    for ax in axes:
        extent = ax.get_window_extent()
        # Convert Matplotlib's bottom-origin canvas coordinates to saved-image
        # coordinates after the tight crop using the content bounds.
        matrix_boxes.append(
            {
                "width_px_before_tight_crop": round(extent.width, 1),
                "height_px_before_tight_crop": round(extent.height, 1),
            }
        )
    # The gridspec gives exact, equal horizontal gaps; report them independently
    # of the tight outer crop.
    gap_px = axes[1].get_window_extent().x0 - axes[0].get_window_extent().x1
    metrics = {
        "saved_png_pixels": [saved_w, saved_h],
        "matrix_boxes": matrix_boxes,
        "inter_matrix_gap_pixels": round(gap_px, 1),
        "inter_matrix_gap_percent_of_saved_width": round(100 * gap_px / saved_w, 3),
        "nonwhite_bounds_saved_png": nonwhite_bounds(saved),
    }
    (HERE / "book_family_adjacency_matrices_layout.json").write_text(
        json.dumps(metrics, indent=2) + "\n"
    )
    print(json.dumps(metrics, indent=2))
    plt.close(fig)


if __name__ == "__main__":
    main()
