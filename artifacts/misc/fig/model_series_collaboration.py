#!/usr/bin/env python3
"""Draw collaboration patterns among the 28 spotlight results.

The audited aggregate values are embedded. The script reads no external data
and writes a vector PDF beside itself.
"""

from pathlib import Path
import os
import tempfile

os.environ.setdefault("MPLCONFIGDIR", os.path.join(tempfile.gettempdir(), "model_collaboration_mplconfig"))
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

OUT = Path(__file__).resolve().parent
LABELS = ["Single agent", "Several agents,\none model family", "Claude + GPT",
          "Claude + Gemini", "Claude + GPT +\nGemini"]
VALUES = [9, 6, 7, 2, 4]
TOTAL = 28
INK, MID, GRID = "#22262A", "#62686D", "#D4D6D8"
COLORS = ["#E7E9EB", "#858C92", "#1B9E77", "#D95F02", "#2C61B4"]

plt.rcParams.update({"font.family": "sans-serif", "font.sans-serif": ["DejaVu Sans"],
                     "font.size": 9.0, "axes.labelweight": "bold",
                     "figure.facecolor": "white",
                     "savefig.facecolor": "white", "savefig.bbox": None,
                     "pdf.fonttype": 42, "ps.fonttype": 42})


def main():
    assert sum(VALUES) == TOTAL
    fig, ax = plt.subplots(figsize=(3.20, 1.78))
    y = range(len(LABELS))
    ax.barh(y, VALUES, height=0.55, color=COLORS, edgecolor="white", linewidth=0.5)
    for yi, value in zip(y, VALUES):
        ax.text(value + 0.25, yi, f"{value} ({100 * value / TOTAL:.0f}%)",
                ha="left", va="center", fontsize=8.0, color=INK, fontweight="bold")
    ax.set_yticks(list(y), LABELS)
    ax.invert_yaxis()
    ax.set_xlim(0, 13.5)
    ax.set_xticks([0, 5, 10])
    ax.set_xlabel("Spotlight results", labelpad=2)
    ax.grid(axis="x", color=GRID, linewidth=0.55)
    ax.set_axisbelow(True)
    ax.spines[["top", "right", "left"]].set_visible(False)
    ax.spines["bottom"].set_color(MID)
    ax.tick_params(axis="y", length=0, pad=5, labelsize=7.8)
    ax.tick_params(axis="x", colors=MID, labelsize=7.8)
    fig.subplots_adjust(left=0.42, right=0.98, top=0.98, bottom=0.23)
    path = OUT / "model_series_collaboration.pdf"
    fig.savefig(path, bbox_inches="tight", pad_inches=0.015)
    print(f"wrote {path} ({path.stat().st_size:,} bytes)")
    plt.close(fig)


if __name__ == "__main__":
    main()
