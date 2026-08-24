#!/usr/bin/env python3
"""Render audited Station-mechanism contributions to spotlight results.

All values are embedded, so this script has no data-file or project-local
input dependency. It writes a vector PDF beside itself.
"""

from pathlib import Path
import os
import tempfile

os.environ.setdefault("MPLCONFIGDIR", os.path.join(tempfile.gettempdir(), "station_mechanisms_mplconfig"))

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Patch


HERE = Path(__file__).absolute().parent
OUTPUT = HERE / "station_mechanism_contributions.pdf"

TOTAL = 28
# Ordered by the number of results receiving a direct or indirect contribution.
DATA = [
    ("Holiday", 14, 9, 5),
    ("Archive paper", 18, 3, 7),
    ("Stagnation protocol", 10, 4, 14),
    ("Peer communication", 8, 4, 16),
    ("Supervisor", 8, 4, 16),
    ("Question Room", 5, 2, 21),
]

DIRECT = "#2C61B4"
INDIRECT = "#A9BBE5"
NONE = "#E7E9EB"
INK = "#22262A"
MID_INK = "#62686D"
GRID = "#D4D6D8"

plt.rcParams.update(
    {
        "font.family": "sans-serif",
        "font.sans-serif": ["DejaVu Sans"],
        "font.size": 8.0,
        "axes.labelsize": 9.0,
        "axes.labelweight": "bold",
        "xtick.labelsize": 7.2,
        "ytick.labelsize": 7.6,
        "legend.fontsize": 7.0,
        "axes.linewidth": 0.72,
        "axes.edgecolor": INK,
        "xtick.color": INK,
        "ytick.color": INK,
        "figure.facecolor": "white",
        "savefig.facecolor": "white",
        "savefig.bbox": "tight",
        "savefig.pad_inches": 0.025,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    }
)


def render():
    assert all(direct + indirect + none == TOTAL for _, direct, indirect, none in DATA)

    labels = [row[0] for row in reversed(DATA)]
    direct = [100 * row[1] / TOTAL for row in reversed(DATA)]
    indirect = [100 * row[2] / TOTAL for row in reversed(DATA)]
    none = [100 * row[3] / TOTAL for row in reversed(DATA)]
    counts = [(row[1], row[2], row[3]) for row in reversed(DATA)]
    y = list(range(len(labels)))

    # A wide, compact canvas lets the paper use the full text width without
    # increasing the figure's vertical footprint.
    fig, ax = plt.subplots(figsize=(7.4, 2.25))
    ax.barh(
        y,
        direct,
        height=0.66,
        color=DIRECT,
        edgecolor="white",
        linewidth=0.65,
        label="Direct contribution",
        zorder=3,
    )
    ax.barh(
        y,
        indirect,
        left=direct,
        height=0.66,
        color=INDIRECT,
        edgecolor="white",
        linewidth=0.65,
        label="Indirect contribution",
        zorder=3,
    )
    ax.barh(
        y,
        none,
        left=[a + b for a, b in zip(direct, indirect)],
        height=0.66,
        color=NONE,
        edgecolor="white",
        linewidth=0.65,
        label="No material contribution",
        zorder=3,
    )

    for yy, (direct_count, indirect_count, none_count), a, b, c in zip(
        y, counts, direct, indirect, none
    ):
        segments = [
            (a / 2, direct_count, "white"),
            (a + b / 2, indirect_count, INK),
            (a + b + c / 2, none_count, MID_INK),
        ]
        for xx, count, color in segments:
            ax.text(
                xx,
                yy,
                str(count),
                ha="center",
                va="center",
                fontsize=7.1,
                fontweight="bold",
                color=color,
                zorder=4,
            )

    ax.set_xlim(0, 100)
    ax.set_xticks([0, 20, 40, 60, 80, 100], ["0", "20", "40", "60", "80", "100%"])
    ax.set_yticks(y, labels)
    ax.set_xlabel("Share of spotlight results")
    ax.tick_params(axis="y", length=0, pad=7)
    ax.grid(axis="x", color=GRID, linestyle=":", linewidth=0.5)
    ax.set_axisbelow(True)
    for side in ("top", "right", "left"):
        ax.spines[side].set_visible(False)

    fig.legend(
        handles=[
            Patch(facecolor=DIRECT, edgecolor=INK, label="Direct contribution"),
            Patch(facecolor=INDIRECT, edgecolor="white", label="Indirect contribution"),
            Patch(facecolor=NONE, edgecolor="white", label="No material contribution"),
        ],
        loc="lower center",
        bbox_to_anchor=(0.60, 0.005),
        frameon=False,
        ncol=3,
        handlelength=1.2,
        columnspacing=1.35,
    )
    fig.subplots_adjust(left=0.245, right=0.99, top=0.98, bottom=0.31)
    fig.savefig(OUTPUT)
    print(f"wrote {OUTPUT} ({OUTPUT.stat().st_size:,} bytes)")
    plt.close(fig)


if __name__ == "__main__":
    render()
