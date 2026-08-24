#!/usr/bin/env python3
"""Draw the Archive-mediated collaboration behind finite-Kakeya S1.

All audited events are embedded. The script reads no external data and writes
a vector PDF beside itself.
"""

from pathlib import Path
import os
import tempfile

os.environ.setdefault("MPLCONFIGDIR", os.path.join(tempfile.gettempdir(), "kakeya_archive_spine_mplconfig"))

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch, Polygon, Rectangle
from matplotlib.transforms import Bbox


OUT = Path(__file__).absolute().parent
STEM = OUT / "finite_kakeya_collaboration_archive_spine"

INK = "#22262A"
MID = "#62686D"
GRID = "#D4D6D8"
PALE = "#F3F4F5"
CLAUDE = "#2C61B4"
GPT = "#1B9E77"
GEMINI = "#D95F02"

TICK_X = 0.28
CARD_X = 2.10
CARD_WIDTH = 3.15
ARCHIVE_X = 4.35

# The 1,213-tick interval is compressed while exact event ticks are retained.
Y = {
    1041: 0.50,
    1244: 1.27,
    1416: 2.04,
    2629: 3.20,
    2633: 4.44,
    2641: 4.88,
}

plt.rcParams.update(
    {
        "font.family": "sans-serif",
        "font.sans-serif": ["DejaVu Sans"],
        "font.size": 9.0,
        "figure.facecolor": "white",
        "savefig.facecolor": "white",
        "savefig.bbox": None,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    }
)


def contribution_card(
    ax,
    tick,
    name,
    model,
    description,
    color,
    *,
    height=0.58,
    description_size=7.25,
):
    """Draw one agent contribution aligned with its event tick."""
    y = Y[tick]
    x = CARD_X
    width = CARD_WIDTH
    left = x - width / 2
    top = y - height / 2
    base = FancyBboxPatch(
        (x - width / 2, y - height / 2),
        width,
        height,
        boxstyle="round,pad=0.02,rounding_size=0.035",
        facecolor=color,
        edgecolor="none",
        linewidth=0,
        zorder=6,
    )
    ax.add_patch(base)
    white_fill = Rectangle(
        (left + 0.040, top),
        width - 0.040,
        height,
        facecolor="white",
        edgecolor="none",
        zorder=7,
    )
    white_fill.set_clip_path(base)
    ax.add_patch(white_fill)
    outline = FancyBboxPatch(
        (left, top),
        width,
        height,
        boxstyle="round,pad=0.02,rounding_size=0.035",
        facecolor="none",
        edgecolor=color,
        linewidth=0.95,
        zorder=8,
    )
    ax.add_patch(outline)
    ax.text(
        x - width * 0.44,
        y - height * 0.20,
        name,
        ha="left",
        va="center",
        fontsize=8.0,
        fontstyle="italic",
        fontweight="bold",
        color=INK,
        zorder=9,
    )
    ax.text(
        x + width * 0.44,
        y - height * 0.20,
        model,
        ha="right",
        va="center",
        fontsize=7.0,
        color=color,
        zorder=9,
    )
    ax.text(
        x,
        y + height * 0.21,
        description,
        ha="center",
        va="center",
        fontsize=description_size,
        linespacing=1.12,
        color=INK,
        zorder=9,
    )
    return {
        "left": x - width / 2,
        "right": x + width / 2,
        "top": y - height / 2,
        "bottom": y + height / 2,
        "center": (x, y),
    }


def arrow(ax, start, end, *, color, style="solid", rad=0.0, zorder=4):
    """Draw an arrow whose shaft terminates exactly at its arrowhead."""
    linestyle = {
        "solid": "solid",
        "dashed": (0, (4.0, 2.5)),
        "dotted": (0, (1.0, 2.2)),
    }[style]
    ax.add_patch(
        FancyArrowPatch(
            start,
            end,
            arrowstyle="-|>",
            mutation_scale=9.0,
            linewidth=1.10,
            linestyle=linestyle,
            color=color,
            connectionstyle=f"arc3,rad={rad}",
            shrinkA=0,
            shrinkB=0,
            zorder=zorder,
        )
    )


def archive_use_arrow(ax, start, end, *, color):
    """Draw a truncated dashed shaft with a left-pointing head at the card."""
    tip_x, tip_y = end
    base_x = tip_x + 0.10
    approach_x = base_x + 0.16
    ax.plot(
        [start[0], approach_x, base_x],
        [start[1], tip_y, tip_y],
        color=color,
        linestyle=(0, (4.0, 2.5)),
        linewidth=1.10,
        dash_capstyle="butt",
        zorder=8,
    )
    ax.add_patch(
        Polygon(
            [(tip_x, tip_y), (base_x, tip_y - 0.065), (base_x, tip_y + 0.065)],
            closed=True,
            facecolor=color,
            edgecolor=color,
            linewidth=0,
            zorder=9,
        )
    )


def direct_mail_arrow(ax, start, end, *, color):
    """Draw a truncated dotted shaft with a downward head at the card border."""
    tip_x, tip_y = end
    base_y = tip_y - 0.13
    ax.plot(
        [start[0], tip_x],
        [start[1], base_y],
        color=color,
        linestyle=(0, (1.0, 2.2)),
        linewidth=1.10,
        dash_capstyle="butt",
        zorder=8,
    )
    ax.add_patch(
        Polygon(
            [(tip_x, tip_y), (tip_x - 0.025, base_y), (tip_x + 0.025, base_y)],
            closed=True,
            facecolor=color,
            edgecolor=color,
            linewidth=0,
            zorder=9,
        )
    )


def archive_node(ax, tick, number, color):
    y = Y[tick]
    ax.text(
        ARCHIVE_X,
        y,
        f"#{number}",
        ha="center",
        va="center",
        fontsize=7.4,
        fontweight="bold",
        color=color,
        bbox={
            "boxstyle": "round,pad=0.24",
            "facecolor": "white",
            "edgecolor": color,
            "linewidth": 1.10,
        },
        zorder=10,
    )


def render():
    fig, ax = plt.subplots(figsize=(5.25, 3.50))
    ax.set_xlim(-0.05, 5.02)
    ax.set_ylim(5.50, -0.35)

    ax.text(TICK_X, -0.17, "Tick", ha="center", va="center",
            fontsize=9.0, fontweight="bold", color=INK)
    ax.text(CARD_X, -0.17, "Agent contribution", ha="center", va="center",
            fontsize=9.0, fontweight="bold", color=INK)
    ax.text(ARCHIVE_X, -0.17, "Archive paper", ha="center", va="center",
            fontsize=9.0, fontweight="bold", color=INK)

    # Archive timeline in the rightmost column.
    ax.fill_betweenx([0.12, 5.10], ARCHIVE_X - 0.08, ARCHIVE_X + 0.08,
                     color="#F1F5FA", zorder=0)
    ax.plot([ARCHIVE_X, ARCHIVE_X], [0.12, 5.10], color="#A8B9D6",
            linewidth=2.1, zorder=1)

    for tick, y in Y.items():
        ax.plot([0.16, 6.40], [y, y], color=PALE, linewidth=0.55, zorder=0)
        ax.text(TICK_X, y, str(tick), ha="center", va="center",
                fontsize=7.7, color=MID, zorder=8)

    break_y = 2.70
    ax.plot(
        [ARCHIVE_X - 0.08, ARCHIVE_X + 0.08],
        [break_y - 0.06, break_y + 0.06],
        color=MID,
        linewidth=0.8,
        zorder=8,
    )
    ax.plot(
        [ARCHIVE_X - 0.08, ARCHIVE_X + 0.08],
        [break_y + 0.04, break_y + 0.16],
        color=MID,
        linewidth=0.8,
        zorder=8,
    )
    symploke = contribution_card(
        ax,
        1041,
        "Symploke IV",
        "Claude 4.8",
        "Published a conic/character-sum method for inversion maps",
        CLAUDE,
    )
    bourbaki = contribution_card(
        ax,
        1244,
        "Bourbaki IV",
        "Gemini 3.1 Pro",
        "Published the fractional-linear construction family",
        GEMINI,
    )
    parallax = contribution_card(
        ax,
        1416,
        "Parallax II",
        "GPT-5.5",
        "Published square-class structure; isolated the open count",
        GPT,
    )
    noesis = contribution_card(
        ax,
        2629,
        "Noesis III",
        "GPT-5.5",
        "Mail asking for an exact formula and coverage proof",
        GPT,
    )
    daedalus = contribution_card(
        ax,
        2633,
        "Daedalus XIV",
        "Claude 4.8",
        "Combined #72's method, #91's family, and #102's analysis\n"
        "into an exact formula and all-prime proof",
        CLAUDE,
        height=0.82,
        description_size=6.9,
    )

    archive_node(ax, 1041, 72, CLAUDE)
    archive_node(ax, 1244, 91, GEMINI)
    archive_node(ax, 1416, 102, GPT)
    archive_node(ax, 2641, 160, CLAUDE)

    # Solid publication arrows approach the left edge of each Archive node.
    node_left = ARCHIVE_X - 0.17
    arrow(ax, (symploke["right"] + 0.03, Y[1041]), (node_left, Y[1041]),
          color=CLAUDE)
    arrow(ax, (bourbaki["right"] + 0.03, Y[1244]), (node_left, Y[1244]),
          color=GEMINI)
    arrow(ax, (parallax["right"] + 0.03, Y[1416]), (node_left, Y[1416]),
          color=GPT)
    arrow(
        ax,
        (daedalus["right"] + 0.03, daedalus["bottom"] - 0.05),
        (node_left, Y[2641]),
        color=CLAUDE,
        rad=-0.10,
    )

    # Dashed Archive-use arrows leave from below each node, physically
    # separated from the incoming publication arrow and its arrowhead.
    node_departure_x = ARCHIVE_X - 0.02
    archive_use_arrow(
        ax,
        (node_departure_x, Y[1041] + 0.20),
        (daedalus["right"], Y[2633] - 0.16),
        color=CLAUDE,
    )
    archive_use_arrow(
        ax,
        (node_departure_x, Y[1244] + 0.20),
        (daedalus["right"], Y[2633]),
        color=GEMINI,
    )
    archive_use_arrow(
        ax,
        (node_departure_x, Y[1416] + 0.20),
        (daedalus["right"], Y[2633] + 0.16),
        color=GPT,
    )

    # Dotted direct-mail arrow bypasses the Archive column.
    direct_mail_arrow(
        ax,
        (noesis["center"][0], noesis["bottom"] + 0.05),
        (daedalus["center"][0], daedalus["top"]),
        color=GPT,
    )

    ax.legend(
        handles=[
            Line2D([0], [0], color=MID, linewidth=1.1,
                   label="Published as archive paper"),
            Line2D([0], [0], color=MID, linewidth=1.1,
                   linestyle=(0, (4.0, 2.5)), label="Later use of archive paper"),
            Line2D([0], [0], color=MID, linewidth=1.1,
                   linestyle=(0, (1.0, 2.2)), label="Direct mail"),
        ],
        loc="lower center",
        bbox_to_anchor=(0.5, -0.025),
        frameon=False,
        ncol=3,
        fontsize=7.9,
        handlelength=1.7,
        columnspacing=0.95,
    )
    ax.axis("off")
    fig.subplots_adjust(left=0.025, right=0.985, top=0.98, bottom=0.12)

    path = Path(f"{STEM}.pdf")
    # Remove only unused space below the legend so that the LaTeX subcaption
    # sits close to the timeline; preserve the top and horizontal geometry.
    fig.savefig(
        path,
        bbox_inches=Bbox.from_bounds(0.0, 0.30, 5.25, 3.20),
    )
    print(f"wrote {path} ({path.stat().st_size:,} bytes)")
    plt.close(fig)


if __name__ == "__main__":
    render()
