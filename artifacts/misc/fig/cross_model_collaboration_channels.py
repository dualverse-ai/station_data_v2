#!/usr/bin/env python3
"""Draw the main communication channel for 13 cross-model results.

The dialogue-audited values are embedded. Each result is assigned to its most
important channel. The script reads no external data and writes a vector PDF
beside itself.
"""

from pathlib import Path
import os
import tempfile

os.environ.setdefault("MPLCONFIGDIR", os.path.join(tempfile.gettempdir(), "cross_model_channels_mplconfig"))
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

OUT = Path(__file__).resolve().parent
CHANNELS = ["Archive Room", "Mail Room", "Research Center", "Question Room"]
VALUES = [8, 2, 2, 1]
TOTAL = 13
INK, MID, GRID = "#22262A", "#62686D", "#D4D6D8"
COLORS = ["#2C61B4", "#1B9E77", "#7570B3", "#D95F02"]

plt.rcParams.update({"font.family": "sans-serif", "font.sans-serif": ["DejaVu Sans"],
                     "font.size": 9.0, "axes.labelweight": "bold",
                     "figure.facecolor": "white",
                     "savefig.facecolor": "white", "savefig.bbox": None,
                     "pdf.fonttype": 42, "ps.fonttype": 42})


def main():
    assert sum(VALUES) == TOTAL
    fig, ax = plt.subplots(figsize=(3.20, 1.52))
    y = range(len(CHANNELS))
    ax.barh(y, VALUES, height=0.55, color=COLORS, edgecolor="white", linewidth=0.5)
    for yi, value in zip(y, VALUES):
        ax.text(value + 0.22, yi, f"{value} ({100 * value / TOTAL:.0f}%)",
                ha="left", va="center", fontsize=8.0, color=INK, fontweight="bold")
    ax.set_yticks(list(y), CHANNELS)
    ax.invert_yaxis()
    ax.set_xlim(0, 12)
    ax.set_xticks([0, 5, 10])
    ax.set_xlabel("Cross-model spotlight\nresults", labelpad=2, linespacing=0.95)
    ax.grid(axis="x", color=GRID, linewidth=0.55)
    ax.set_axisbelow(True)
    ax.spines[["top", "right", "left"]].set_visible(False)
    ax.spines["bottom"].set_color(MID)
    ax.tick_params(axis="y", length=0, pad=5, labelsize=7.8)
    ax.tick_params(axis="x", colors=MID, labelsize=7.8)
    fig.subplots_adjust(left=0.42, right=0.98, top=0.98, bottom=0.27)
    path = OUT / "cross_model_collaboration_channels.pdf"
    fig.savefig(path, bbox_inches="tight", pad_inches=0.015)
    print(f"wrote {path} ({path.stat().st_size:,} bytes)")
    plt.close(fig)


if __name__ == "__main__":
    main()
