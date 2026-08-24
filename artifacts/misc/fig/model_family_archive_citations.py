#!/usr/bin/env python3
"""Render later archive paper citations received by model family.

The audited aggregate values are embedded so this paper figure is standalone.
One citation is one unique later citing-paper/cited-paper pair; repeated mentions
within the same paper count once. The script writes a vector PDF beside itself.
"""

from pathlib import Path
import os
import tempfile

os.environ.setdefault("MPLCONFIGDIR", os.path.join(tempfile.gettempdir(), "model_family_citations_mplconfig"))

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


HERE = Path(__file__).resolve().parent
STEM = HERE / "model_family_archive_citations"

# Reverse plotting order makes the displayed top-to-bottom order Claude, GPT,
# Gemini, consistent with the companion panels.
FAMILIES = ["Gemini", "GPT", "Claude"]
CITATIONS = {"Claude": 6592, "GPT": 2582, "Gemini": 2750}
ACCEPTED_PAPERS = {"Claude": 696, "GPT": 388, "Gemini": 508}
COLORS = {"Claude": "#2C61B4", "GPT": "#1B9E77", "Gemini": "#D95F02"}
INK = "#22262A"
GRID = "#D4D6D8"

plt.rcParams.update(
    {
        "font.family": "sans-serif",
        "font.sans-serif": ["DejaVu Sans"],
        "font.size": 10.0,
        "axes.labelsize": 9.0,
        "axes.labelweight": "bold",
        "xtick.labelsize": 9.5,
        "ytick.labelsize": 10.0,
        "axes.linewidth": 0.72,
        "axes.edgecolor": INK,
        "xtick.color": INK,
        "ytick.color": INK,
        "xtick.direction": "out",
        "ytick.direction": "out",
        "xtick.major.width": 0.7,
        "ytick.major.width": 0.7,
        "figure.facecolor": "white",
        "savefig.facecolor": "white",
        "savefig.bbox": None,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    }
)


def render():
    assert sum(CITATIONS.values()) == 11924
    assert sum(ACCEPTED_PAPERS.values()) == 1592
    y = range(len(FAMILIES))
    fig, ax = plt.subplots(figsize=(3.45, 2.20))
    bars = ax.barh(
        y,
        [CITATIONS[family] for family in FAMILIES],
        height=0.60,
        color=[COLORS[family] for family in FAMILIES],
        edgecolor=INK,
        linewidth=0.48,
    )
    for bar, family in zip(bars, FAMILIES):
        citations = CITATIONS[family]
        rate = citations / ACCEPTED_PAPERS[family]
        ax.text(
            citations + 120,
            bar.get_y() + bar.get_height() / 2,
            f"{citations:,}\n({rate:.1f} per paper)",
            va="center",
            ha="left",
            fontsize=9.8,
            linespacing=1.0,
            color=INK,
        )

    ax.set_yticks(list(y), FAMILIES)
    ax.set_xlim(0, 11500)
    ax.set_xticks([0, 2000, 4000, 6000, 8000])
    ax.set_xlabel("Citations from later archive papers", labelpad=6)
    ax.set_ylabel("Archive paper model", labelpad=10)
    ax.tick_params(axis="y", length=0, pad=7)
    ax.grid(axis="x", color=GRID, linestyle=":", linewidth=0.5)
    ax.set_axisbelow(True)
    for side in ("top", "right", "left"):
        ax.spines[side].set_visible(False)
    fig.subplots_adjust(left=0.29, right=0.98, top=0.963, bottom=0.39)

    path = Path(f"{STEM}.pdf")
    fig.savefig(path)
    print(f"wrote {path} ({path.stat().st_size:,} bytes)")
    plt.close(fig)


if __name__ == "__main__":
    render()
