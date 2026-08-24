#!/usr/bin/env python3
"""Render the evaluation ticks of the 28 spotlight results.

All audited values are embedded, so this script has no data-file or
project-local input dependency. It writes a vector PDF beside itself.
"""

from pathlib import Path
from collections import defaultdict
import math
import os
import tempfile

os.environ.setdefault("MPLCONFIGDIR", os.path.join(tempfile.gettempdir(), "discovery_timeline_mplconfig"))

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.transforms as transforms
from matplotlib.lines import Line2D


HERE = Path(__file__).absolute().parent
OUTPUT = HERE / "discovery_timeline.pdf"

# Problem names follow the paragraph/subsection names in the paper.
PROBLEMS = [
    ("finite_kakeya", "Finite-field Kakeya"),
    ("autocorr_6_5", "Erdős minimum overlap"),
    ("kissing", "Kissing number in d=11"),
    ("kakeya_needle", "Discretized Kakeya needle"),
    ("uncertainty", "Sign uncertainty principle"),
    ("hardy_littlewood", "Hardy–Littlewood\nmaximal inequality"),
    ("ovals", "Ovals problem"),
    ("prime_number_theorem", "Prime number theorem"),
    ("difference_basis", "Difference bases"),
    ("autocorr_6_3", "Flat autoconvolution"),
    ("book", "Book Ramsey numbers"),
    ("jacobian", "Jacobian Conjecture"),
]

# One entry per audited spotlight result: (problem key, spotlight label,
# decisive evaluation-submission tick). For purely theoretical results whose
# decisive step was reviewed as an archive submission rather than a Research
# Center evaluation, the archive-review tick is used.
POINTS = [
    ("finite_kakeya", "S1", 2631),
    ("finite_kakeya", "S2", 2751),
    ("finite_kakeya", "S3", 2638),
    ("autocorr_6_5", "S1", 693),
    ("kissing", "S1", 1145),
    ("kissing", "S1", 1471),
    ("kissing", "S1", 924),
    ("kissing", "S2", 1164),
    ("kissing", "S3", 911),
    ("kissing", "S3", 1608),
    ("kakeya_needle", "S1", 391),
    ("kakeya_needle", "S2", 63),
    ("kakeya_needle", "S2", 392),
    ("kakeya_needle", "S2", 1323),
    ("kakeya_needle", "S2", 1328),
    ("uncertainty", "S1", 1332),
    ("uncertainty", "S2", 671),
    ("hardy_littlewood", "S1", 735),
    ("ovals", "S1", 15),
    ("prime_number_theorem", "S1", 453),
    ("prime_number_theorem", "S2", 174),
    ("difference_basis", "S1", 31),
    ("autocorr_6_3", "S1", 944),
    ("book", "S1", 3727),
    ("book", "S2", 1226),
    ("book", "S3", 2495),
    ("jacobian", "S1", 36),
    ("jacobian", "S2", 38),
]

COLORS = {"S1": "#2C61B4", "S2": "#1B9E77", "S3": "#D95F02"}
INK = "#22262A"
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
    assert len(POINTS) == 28
    assert sum(tick > 1000 for _, _, tick in POINTS) == 13
    assert {label for _, label, _ in POINTS} == set(COLORS)

    y_map = {key: len(PROBLEMS) - 1 - index for index, (key, _) in enumerate(PROBLEMS)}
    fig, ax = plt.subplots(figsize=(7.4, 3.75))

    for problem, _ in PROBLEMS:
        ax.hlines(
            y_map[problem],
            8,
            4600,
            color=GRID,
            linewidth=0.55,
            zorder=0,
        )

    # Closely spaced ticks would otherwise hide one another at paper scale.
    # A small horizontal display offset keeps every circle visible while all
    # circles remain centered vertically on their problem's guide line.
    by_problem = defaultdict(list)
    for point in POINTS:
        by_problem[point[0]].append(point)

    display_offsets = {}
    for problem, problem_points in by_problem.items():
        ordered = sorted(problem_points, key=lambda point: point[2])
        clusters = []
        cluster = []
        for point in ordered:
            if cluster and math.log10(point[2]) - math.log10(cluster[-1][2]) >= 0.035:
                clusters.append(cluster)
                cluster = []
            cluster.append(point)
        clusters.append(cluster)
        for close_points in clusters:
            for index, point in enumerate(close_points):
                display_offsets[id(point)] = (index - (len(close_points) - 1) / 2) * 5.2

    for point in POINTS:
        problem, label, tick = point
        marker_transform = transforms.offset_copy(
            ax.transData,
            fig=fig,
            x=display_offsets[id(point)],
            units="points",
        )
        ax.plot(
            [tick],
            [y_map[problem]],
            marker="o",
            linestyle="none",
            markersize=5.8,
            markerfacecolor=COLORS[label],
            markeredgecolor=INK,
            markeredgewidth=0.5,
            transform=marker_transform,
            zorder=3,
        )

    ax.set_xscale("log")
    tick_values = [10, 30, 100, 300, 1000, 3000]
    ax.set_xticks(tick_values, [str(value) for value in tick_values])
    ax.set_xlim(8, 4600)
    ax.set_ylim(-0.55, len(PROBLEMS) - 0.45)
    ax.set_yticks(
        [y_map[key] for key, _ in PROBLEMS],
        [label for _, label in PROBLEMS],
    )
    ax.set_xlabel("Discovery tick (log scale)")
    ax.tick_params(axis="y", length=0, pad=7)
    ax.grid(axis="x", which="major", color=GRID, linestyle=":", linewidth=0.5)
    ax.set_axisbelow(True)
    for side in ("top", "right", "left"):
        ax.spines[side].set_visible(False)

    handles = [
        Line2D(
            [],
            [],
            marker="o",
            linestyle="none",
            markersize=5.2,
            markerfacecolor=COLORS[label],
            markeredgecolor=INK,
            markeredgewidth=0.5,
            label=label,
        )
        for label in ("S1", "S2", "S3")
    ]
    ax.legend(
        handles=handles,
        loc="lower center",
        bbox_to_anchor=(0.5, 1.01),
        ncol=3,
        frameon=False,
        handletextpad=0.35,
        columnspacing=1.0,
    )

    fig.subplots_adjust(left=0.275, right=0.99, top=0.91, bottom=0.15)
    fig.savefig(OUTPUT)
    print(f"wrote {OUTPUT} ({OUTPUT.stat().st_size:,} bytes)")
    plt.close(fig)


if __name__ == "__main__":
    render()
