#!/usr/bin/env python3
"""Render primary spotlight discoveries by model family.

The audited aggregate data are embedded so the script has no data-file or
project-local input dependency. It writes a vector PDF beside itself.
"""

from pathlib import Path
import os
import tempfile

os.environ.setdefault("MPLCONFIGDIR", os.path.join(tempfile.gettempdir(), "model_family_primary_mplconfig"))

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


# Keep the user-facing /home path instead of resolving its Windows mount
# target; the workspace grants writes through this path.
HERE = Path(__file__).absolute().parent
STEM = HERE / "model_family_primary_discoveries"

# Top-to-bottom display order is fixed as Claude, GPT, Gemini.
FAMILIES = ["Gemini", "GPT", "Claude"]
VALUES = {"Claude": 18, "GPT": 9, "Gemini": 1}
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
        # Keep a fixed canvas so the plotting rectangle aligns exactly with
        # the companion Archive panel when the PDFs are placed side by side.
        "savefig.bbox": None,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    }
)


def render():
    total = sum(VALUES.values())
    assert total == 28
    y = range(len(FAMILIES))

    fig, ax = plt.subplots(figsize=(3.45, 2.20))
    bars = ax.barh(
        y,
        [VALUES[family] for family in FAMILIES],
        height=0.60,
        color=[COLORS[family] for family in FAMILIES],
        edgecolor=INK,
        linewidth=0.48,
    )
    for bar, family in zip(bars, FAMILIES):
        value = VALUES[family]
        ax.text(
            value + 0.22,
            bar.get_y() + bar.get_height() / 2,
            f"{value}  ({100 * value / total:.0f}%)",
            va="center",
            fontsize=9.8,
            color=INK,
        )

    ax.set_yticks(list(y), FAMILIES)
    ax.set_xlim(0, 24)
    ax.set_xlabel("Spotlight results", labelpad=6)
    ax.set_ylabel("Agent's model", labelpad=10)
    ax.tick_params(axis="y", length=0, pad=7)
    ax.grid(axis="x", color=GRID, linestyle=":", linewidth=0.5)
    ax.set_axisbelow(True)
    for side in ("top", "right", "left"):
        ax.spines[side].set_visible(False)
    # Reserve a compact bottom legend band shared with the companion panel.
    # These bounds preserve the original axes rectangle in physical units and
    # its distance from the top edge.
    fig.subplots_adjust(left=0.29, right=0.98, top=0.963, bottom=0.39)

    path = Path(f"{STEM}.pdf")
    fig.savefig(path)
    print(f"wrote {path} ({path.stat().st_size:,} bytes)")
    plt.close(fig)


if __name__ == "__main__":
    render()
