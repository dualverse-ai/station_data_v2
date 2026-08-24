#!/usr/bin/env python3
"""Render Archive submissions and acceptances by model family.

The audited aggregate data are embedded so the script has no data-file or
project-local input dependency. It writes a vector PDF beside itself.
"""

from pathlib import Path
import os
import tempfile

os.environ.setdefault("MPLCONFIGDIR", os.path.join(tempfile.gettempdir(), "model_family_archive_mplconfig"))

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Patch


# Keep the user-facing /home path instead of resolving its Windows mount
# target; the workspace grants writes through this path.
HERE = Path(__file__).absolute().parent
STEM = HERE / "model_family_archive_submissions"

# Top-to-bottom display order is fixed as Claude, GPT, Gemini.
FAMILIES = ["Gemini", "GPT", "Claude"]
TOTAL = {"Claude": 1236, "GPT": 506, "Gemini": 2652}
ACCEPTED = {"Claude": 696, "GPT": 388, "Gemini": 508}
COLORS = {"Claude": "#2C61B4", "GPT": "#1B9E77", "Gemini": "#D95F02"}
INK = "#22262A"
MID_INK = "#62686D"
LIGHT_INK = "#AEB4BA"
PALE_GREY = "#E7E9EB"
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
        "legend.fontsize": 10.0,
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
        # Keep the same fixed canvas and plotting rectangle as the companion
        # discovery panel; tight cropping rescales the panels differently.
        "savefig.bbox": None,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    }
)


def render():
    assert sum(TOTAL.values()) == 4394
    assert sum(ACCEPTED.values()) == 1592
    y = range(len(FAMILIES))

    fig, ax = plt.subplots(figsize=(3.45, 2.20))
    ax.barh(
        y,
        [TOTAL[family] for family in FAMILIES],
        height=0.60,
        color=PALE_GREY,
        edgecolor=LIGHT_INK,
        linewidth=0.5,
        zorder=2,
    )
    ax.barh(
        y,
        [ACCEPTED[family] for family in FAMILIES],
        height=0.60,
        color=[COLORS[family] for family in FAMILIES],
        edgecolor=INK,
        linewidth=0.5,
        zorder=3,
    )
    for yy, family in zip(y, FAMILIES):
        total = TOTAL[family]
        accepted = ACCEPTED[family]
        ax.text(
            total + 50,
            yy,
            f"{accepted:,} / {total:,}\n({100 * accepted / total:.1f}%)",
            va="center",
            ha="left",
            fontsize=9.8,
            linespacing=1.18,
            color=INK,
        )

    ax.set_yticks(list(y), FAMILIES)
    ax.set_xlim(0, 4000)
    ax.set_xticks([0, 1000, 2000, 3000])
    ax.set_xlabel("Archive paper submission counts", labelpad=6)
    ax.set_ylabel("Agent's model", labelpad=10)
    ax.tick_params(axis="y", length=0, pad=7)
    ax.grid(axis="x", color=GRID, linestyle=":", linewidth=0.5)
    ax.set_axisbelow(True)
    for side in ("top", "right", "left"):
        ax.spines[side].set_visible(False)
    fig.legend(
        handles=[
            Patch(facecolor=PALE_GREY, edgecolor=LIGHT_INK, label="All submissions"),
            Patch(facecolor=MID_INK, edgecolor=INK, label="Accepted"),
        ],
        loc="lower center",
        bbox_to_anchor=(0.635, 0.008),
        frameon=False,
        ncol=2,
        handlelength=1.2,
        columnspacing=1.2,
    )
    # Match the companion panel's axes rectangle exactly while reserving a
    # compact bottom band for the one-row legend.
    fig.subplots_adjust(left=0.29, right=0.98, top=0.963, bottom=0.39)

    path = Path(f"{STEM}.pdf")
    fig.savefig(path)
    print(f"wrote {path} ({path.stat().st_size:,} bytes)")
    plt.close(fig)


if __name__ == "__main__":
    render()
