#!/usr/bin/env python3
"""Plot the best exact-certified kissing lower bound in three Station runs.

All audited values are embedded, so this script has no data-file or
project-local input dependency. It writes a vector PDF beside itself.
"""

from pathlib import Path
import os
import tempfile

os.environ.setdefault("MPLCONFIGDIR", os.path.join(tempfile.gettempdir(), "kissing_reproducibility_mplconfig"))

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


HERE = Path(__file__).absolute().parent
OUTPUT = HERE / "kissing_reproducibility.pdf"

# Strict improvements in the best exact-certified N. Station 1 continues to
# the later discovery of a second 604-point construction.
RUNS = [
    {
        "label": "Station 1",
        "color": "#2C61B4",
        "records": [(41, 582), (68, 594), (76, 595), (78, 598), (88, 599), (93, 600), (1145, 604)],
        "extra_endpoint": (1471, 604),
        "milestones": [(1145, 604, "Construction 3"), (1471, 604, "Construction 2")],
    },
    {
        "label": "Station 2",
        "color": "#D95F02",
        "records": [(13, 582), (51, 594), (65, 595), (65, 596), (76, 598), (86, 599), (91, 600), (936, 604)],
        "extra_endpoint": None,
        "milestones": [(936, 604, "Construction 1")],
    },
    {
        "label": "Station 3",
        "color": "#1B9E77",
        "records": [
            (42, 582),
            (87, 594),
            (106, 595),
            (215, 596),
            (241, 597),
            (248, 598),
            (251, 599),
            (253, 600),
            (525, 601),
            (531, 603),
            (555, 604),
        ],
        "extra_endpoint": None,
        "milestones": [(555, 604, "Construction 1")],
    },
]

INK = "#22262A"
GRID = "#D4D6D8"

plt.rcParams.update(
    {
        "font.family": "sans-serif",
        "font.sans-serif": ["DejaVu Sans"],
        "font.size": 8.0,
        "axes.labelsize": 9.0,
        "axes.labelweight": "bold",
        "xtick.labelsize": 7.5,
        "ytick.labelsize": 7.5,
        "axes.linewidth": 0.72,
        "axes.edgecolor": INK,
        "xtick.color": INK,
        "ytick.color": INK,
        "figure.facecolor": "white",
        "savefig.facecolor": "white",
        "savefig.bbox": "tight",
        "savefig.pad_inches": 0.03,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    }
)


def render() -> None:
    assert [run["records"][-1][1] for run in RUNS] == [604, 604, 604]

    fig, ax = plt.subplots(figsize=(7.4, 3.0))

    for run in RUNS:
        records = run["records"]
        x = [tick for tick, _ in records]
        y = [bound for _, bound in records]
        if run["extra_endpoint"] is not None:
            x.append(run["extra_endpoint"][0])
            y.append(run["extra_endpoint"][1])
        ax.step(
            x,
            y,
            where="post",
            color=run["color"],
            linewidth=1.75,
            label=run["label"],
            zorder=2,
        )
        ax.scatter(
            [tick for tick, _ in records],
            [bound for _, bound in records],
            s=20,
            color=run["color"],
            edgecolor="white",
            linewidth=0.55,
            zorder=3,
        )
        if run["extra_endpoint"] is not None:
            tick, bound = run["extra_endpoint"]
            ax.scatter(
                [tick],
                [bound],
                marker="D",
                s=32,
                facecolor="white",
                edgecolor=run["color"],
                linewidth=1.2,
                zorder=4,
            )

        for tick, bound, label in run["milestones"]:
            horizontal_alignment = "center"
            x_offset = 0
            if tick == 1471:
                horizontal_alignment = "right"
                x_offset = -3
            ax.annotate(
                label,
                (tick, bound),
                xytext=(x_offset, 7),
                textcoords="offset points",
                ha=horizontal_alignment,
                va="bottom",
                fontsize=7.4,
                color=INK,
                clip_on=False,
            )

    ax.set_ylim(581.4, 605.0)
    ax.set_yticks(list(range(582, 605, 2)))
    ax.set_xlim(0, 1530)
    ax.set_xticks([0, 250, 500, 750, 1000, 1250, 1500])
    ax.set_xlabel("Tick")
    ax.set_ylabel("Best exact lower bound")
    ax.grid(color=GRID, linestyle=":", linewidth=0.5)
    ax.set_axisbelow(True)
    ax.tick_params(axis="y", length=0, pad=5)
    for side in ("top", "right", "left"):
        ax.spines[side].set_visible(False)
    ax.legend(
        loc="lower right",
        frameon=False,
        ncol=1,
        handlelength=2.2,
        handletextpad=0.55,
    )

    fig.subplots_adjust(left=0.105, right=0.995, top=0.985, bottom=0.17)
    fig.savefig(OUTPUT)
    print(f"wrote {OUTPUT} ({OUTPUT.stat().st_size:,} bytes)")
    plt.close(fig)


if __name__ == "__main__":
    render()
