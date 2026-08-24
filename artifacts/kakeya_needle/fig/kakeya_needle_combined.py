#!/usr/bin/env python3
"""Render the dyadic comparison and three n=5 figure alternatives."""

import os
import tempfile
from fractions import Fraction
from pathlib import Path

os.environ.setdefault("MPLCONFIGDIR", os.path.join(tempfile.gettempdir(), "kakeya_needle_mplconfig"))

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import Polygon

OUT = Path(__file__).resolve().parent
OUT.mkdir(parents=True, exist_ok=True)

BLUE = "#2C61B4"
MID_BLUE = "#4E7DC7"
PALE_BLUE = "#D1D9EF"
GOLD = "#B57C00"
PALE_GOLD = "#F5E4B5"
TEAL = "#1B9E77"
GREY = "#707070"
LIGHT_GREY = "#B5B5B5"

PAIR_STYLE = {
    1: (PALE_BLUE, BLUE),
    2: ("#D7ECE5", TEAL),
    3: (PALE_GOLD, GOLD),
    4: ("#D7ECE5", TEAL),
    5: (PALE_BLUE, BLUE),
}

plt.rcParams.update({
    "font.family": "sans-serif",
    "font.sans-serif": ["DejaVu Sans"],
    "mathtext.fontset": "dejavusans",
    "font.size": 7.5,
    "axes.labelsize": 8.5,
    "axes.labelweight": "bold",
    "axes.linewidth": 0.8,
    "xtick.labelsize": 7.0,
    "ytick.labelsize": 7.0,
    "xtick.direction": "out",
    "ytick.direction": "out",
    "figure.facecolor": "white",
    "savefig.facecolor": "white",
    "savefig.bbox": "tight",
    "savefig.pad_inches": 0.02,
    "ps.fonttype": 42,
    "pdf.fonttype": 42,
})

SYMMETRIC = [Fraction(4, 15), Fraction(1, 5), Fraction(2, 15), Fraction(1, 15), Fraction(0)]
ASYMMETRIC_RAW = [Fraction(79, 305), Fraction(47, 305), Fraction(10, 61), Fraction(12, 305), Fraction(0)]

# Translation-align triangle 3. This exposes the unequal reflection axes of
# pairs (1,5) and (2,4) while leaving area unchanged.
ASYMMETRIC = [x + SYMMETRIC[2] - ASYMMETRIC_RAW[2] for x in ASYMMETRIC_RAW]
AXIS = SYMMETRIC[2] + Fraction(1, 10)

DYADIC_N = [2, 4, 8, 16, 32, 64, 128]
STATION_AREA = [
    0.333333333333333, 0.249999999999990, 0.196858619034623,
    0.162715712988193, 0.138596129670274, 0.120900580819172,
    0.107066636561635,
]
AE_AREA = [
    0.333333333333333, 0.250000000000000, 0.196858619034623,
    0.162715712988197, 0.141647494730520, 0.121735177166418,
    0.114810325818618,
]


def vertices(x, j):
    return [(float(x), 0.0), (float(x + Fraction(1, 5)), 0.0),
            (float(x + Fraction(j, 5) - Fraction(1, 2)), 1.0)]


def reflected(poly):
    return [(2.0 * float(AXIS) - x, y) for x, y in poly]


def save(fig, stem):
    for ext, kwargs in (("eps", {"format": "eps"}),
                        ("pdf", {"format": "pdf"}),
                        ("png", {"format": "png", "dpi": 240})):
        fig.savefig(OUT / f"{stem}.{ext}", **kwargs)
    plt.close(fig)


def clean_geometry_axis(ax, show_y=False, show_axis=True):
    ax.set_xlim(-0.082, 0.505)
    ax.set_ylim(-0.015, 1.075)
    # A modest horizontal display expansion keeps the tall sheared triangles
    # legible in a journal column and removes uninformative side whitespace.
    ax.set_aspect(0.55, adjustable="box")
    ax.set_xticks([])
    ax.set_yticks([0, 1] if show_y else [])
    if show_y:
        ax.set_ylabel(r"height $y$")
    for side in ("top", "right", "bottom"):
        ax.spines[side].set_visible(False)
    ax.spines["left"].set_visible(show_y)
    ax.tick_params(length=2.5, pad=2)
    if show_axis:
        ax.axvline(float(AXIS), color="#555555", linewidth=0.6,
                   linestyle=(0, (3, 3)), zorder=7)


def draw_pair_axes(ax, offsets):
    axes = [
        ((offsets[0] + offsets[4] + Fraction(1, 5)) / 2,
         BLUE, (0.0, (5.5, 2.4))),
        ((offsets[1] + offsets[3] + Fraction(1, 5)) / 2,
         TEAL, (1.8, (3.4, 2.1))),
        ((2 * offsets[2] + Fraction(1, 5)) / 2,
         GOLD, (0.8, (1.3, 1.8))),
    ]
    for x, color, style in axes:
        ax.axvline(float(x), color=color, linewidth=0.72,
                   linestyle=style, zorder=7)


def populate_ae_station(ax):
    xs = list(range(len(DYADIC_N)))
    ax.plot(xs, STATION_AREA, color=BLUE, linewidth=1.35, zorder=3)
    ax.plot(xs, AE_AREA, color=TEAL, linewidth=1.2,
            linestyle=(0, (3, 2)), zorder=4)
    ax.plot(xs, AE_AREA, linestyle="none", marker="s", markersize=5.0,
            markerfacecolor=TEAL, markeredgecolor="#0F5B45",
            markeredgewidth=0.5, zorder=5)
    ax.plot(xs, STATION_AREA, linestyle="none", marker="o", markersize=3.3,
            markerfacecolor=BLUE, markeredgecolor="#183664",
            markeredgewidth=0.5, zorder=6)
    ax.set_xticks(xs, [str(n) for n in DYADIC_N])
    ax.set_xlabel(r"number of triangles $n$")
    ax.set_ylabel("union area (lower is better)")
    ax.set_xlim(-0.2, 6.2)
    ax.set_ylim(0.095, 0.35)
    ax.grid(axis="y", color="#CCCCCC", linestyle=":", linewidth=0.5)
    ax.set_axisbelow(True)
    for spine in ax.spines.values():
        spine.set_color("#222222")
    handles = [
        Line2D([], [], color=BLUE, marker="o", markersize=3.3,
               linewidth=1.35, label="Station"),
        Line2D([], [], color=TEAL, marker="s", markersize=4.6,
               linewidth=1.2, linestyle=(0, (3, 2)), label="AlphaEvolve"),
    ]
    ax.legend(handles=handles, loc="upper right", frameon=False,
              fontsize=7.0, handlelength=2.0, borderpad=0.1,
              labelspacing=0.35)


def draw_left_comparison():
    ns = [2, 4, 8, 16, 32, 64, 128]
    station = [
        0.333333333333333, 0.249999999999990, 0.196858619034623,
        0.162715712988193, 0.138596129670274, 0.120900580819172,
        0.107066636561635,
    ]
    alphaevolve = [
        0.333333333333333, 0.250000000000000, 0.196858619034623,
        0.162715712988197, 0.141647494730520, 0.121735177166418,
        0.114810325818618,
    ]
    xs = list(range(len(ns)))
    fig, ax = plt.subplots(figsize=(4.45, 2.65))
    fig.subplots_adjust(left=0.15, right=0.985, bottom=0.20, top=0.96)

    ax.plot(xs, station, color=BLUE, linewidth=1.55, zorder=3)
    ax.plot(xs, alphaevolve, color=TEAL, linewidth=1.35,
            linestyle=(0, (3, 2)), zorder=4)
    ax.plot(xs, alphaevolve, linestyle="none", marker="s", markersize=5.6,
            markerfacecolor=TEAL, markeredgecolor="#0F5B45",
            markeredgewidth=0.55, zorder=5)
    ax.plot(xs, station, linestyle="none", marker="o", markersize=3.6,
            markerfacecolor=BLUE, markeredgecolor="#183664",
            markeredgewidth=0.55, zorder=6)

    # HorizonMath reported only n=128.
    ax.plot([6], [0.1091479892], linestyle="none", marker="D", markersize=5.0,
            markerfacecolor=GOLD, markeredgecolor="#755100",
            markeredgewidth=0.55, zorder=7)

    ax.set_xticks(xs, [str(n) for n in ns])
    ax.set_xlabel(r"number of triangles $n$")
    ax.set_ylabel("union area")
    ax.set_xlim(-0.2, 6.2)
    ax.set_ylim(0.095, 0.35)
    ax.grid(axis="y", color="#CCCCCC", linestyle=":", linewidth=0.5)
    ax.set_axisbelow(True)
    for spine in ax.spines.values():
        spine.set_color("#222222")

    handles = [
        Line2D([], [], color=BLUE, marker="o", markersize=3.6,
               linewidth=1.55, label="Station"),
        Line2D([], [], color=TEAL, marker="s", markersize=5.0,
               linewidth=1.35, linestyle=(0, (3, 2)), label="AlphaEvolve"),
        Line2D([], [], color="none", marker="D", markersize=4.5,
               markerfacecolor=GOLD, markeredgecolor="#755100",
               label="HorizonMath ($n=128$)"),
    ]
    ax.legend(handles=handles, loc="upper right", frameon=False,
              fontsize=6.8, handlelength=2.0, borderpad=0.1, labelspacing=0.35)
    save(fig, "left_dyadic_comparison")


def draw_colored_set(ax, offsets, labels=False, fill=True):
    polygons = []
    for j, x in enumerate(offsets, start=1):
        poly = vertices(x, j)
        polygons.append((j, poly))
        face, edge = PAIR_STYLE[j]
        if fill:
            ax.add_patch(Polygon(poly, closed=True, facecolor=face,
                                 edgecolor="none", zorder=2))
        ax.add_patch(Polygon(poly, closed=True, facecolor="none",
                             edgecolor=edge, linewidth=0.72,
                             joinstyle="round", zorder=4))
        if labels:
            ax.text(poly[2][0], 1.025, str(j), ha="center", va="bottom",
                    fontsize=6.5, color=edge, clip_on=False)
    return polygons


def draw_option_a():
    fig, axes = plt.subplots(1, 2, figsize=(3.85, 2.62), sharey=True)
    fig.subplots_adjust(left=0.105, right=0.995, bottom=0.08,
                        top=0.79, wspace=0.025)
    draw_colored_set(axes[0], SYMMETRIC)
    draw_colored_set(axes[1], ASYMMETRIC)
    clean_geometry_axis(axes[0], show_y=True, show_axis=False)
    clean_geometry_axis(axes[1], show_y=False, show_axis=False)
    draw_pair_axes(axes[0], SYMMETRIC)
    draw_pair_axes(axes[1], ASYMMETRIC)
    axes[0].set_title("Best symmetric\n$A=7/30$", fontsize=7.8,
                      fontweight="normal", pad=3)
    axes[1].set_title("Asymmetric construction\n$A=14/61$", fontsize=7.8,
                      fontweight="normal", pad=3)
    save(fig, "right_option_a_side_by_side")


def draw_combined_figure():
    fig = plt.figure(figsize=(7.4, 2.75))
    outer = fig.add_gridspec(
        1, 2, width_ratios=(1.0, 1.0), wspace=0.16,
        left=0.07, right=0.995, bottom=0.22, top=0.92,
    )
    left = fig.add_subplot(outer[0, 0])
    populate_ae_station(left)

    right_grid = outer[0, 1].subgridspec(1, 2, wspace=0.025)
    right = [fig.add_subplot(right_grid[0, i]) for i in range(2)]
    draw_colored_set(right[0], SYMMETRIC)
    draw_colored_set(right[1], ASYMMETRIC)
    clean_geometry_axis(right[0], show_y=True, show_axis=False)
    clean_geometry_axis(right[1], show_y=False, show_axis=False)
    draw_pair_axes(right[0], SYMMETRIC)
    draw_pair_axes(right[1], ASYMMETRIC)
    right[0].text(0.5, -0.085, "Best symmetric\n$A=7/30$",
                  transform=right[0].transAxes, ha="center", va="top",
                  fontsize=7.6)
    right[1].text(0.5, -0.085, "Asymmetric construction\n$A=14/61$",
                  transform=right[1].transAxes, ha="center", va="top",
                  fontsize=7.6)
    save(fig, "kakeya_needle_combined")


def draw_dashed_set(ax, offsets=None, mirror=False):
    polys = []
    source = ASYMMETRIC if mirror else offsets
    for j, x in enumerate(source, start=1):
        poly = vertices(x, j)
        if mirror:
            poly = reflected(poly)
        polys.append((j, poly))
        ax.add_patch(Polygon(poly, closed=True, facecolor="none",
                             edgecolor=GREY, linewidth=1.0,
                             linestyle=(0, (3, 2)), zorder=5))
    return polys


def apex_guides(ax, first, second):
    for (j, p), (_, q) in zip(first, second):
        x0, x1 = p[2][0], q[2][0]
        if abs(x1 - x0) > 1e-10:
            ax.plot([x0, x1], [1.018, 1.018], color=LIGHT_GREY,
                    linewidth=0.7, zorder=7, clip_on=False)
        _, edge = PAIR_STYLE[j]
        ax.plot([x1], [1.018], marker="o", markersize=2.4,
                markerfacecolor=edge, markeredgewidth=0, zorder=8,
                clip_on=False)
        ax.plot([x0], [1.018], marker="o", markersize=2.8,
                markerfacecolor="white", markeredgecolor=GREY,
                markeredgewidth=0.65, zorder=8, clip_on=False)


def overlay_legend(ax, reference_label):
    handles = [
        Line2D([], [], color=GREY, linewidth=1.0, linestyle=(0, (3, 2)),
               label=reference_label),
        Line2D([], [], color=BLUE, linewidth=1.15,
               label="Asymmetric construction"),
    ]
    ax.legend(handles=handles, loc="lower center", bbox_to_anchor=(0.5, 1.015),
              frameon=False, fontsize=6.5, handlelength=2.2,
              borderpad=0, labelspacing=0.28)


def draw_option_b():
    fig, ax = plt.subplots(figsize=(2.12, 2.62))
    fig.subplots_adjust(left=0.25, right=0.98, bottom=0.075, top=0.79)
    asym = draw_colored_set(ax, ASYMMETRIC)
    sym = draw_dashed_set(ax, offsets=SYMMETRIC)
    # Restore the colored boundaries above the dashed reference.
    draw_colored_set(ax, ASYMMETRIC, fill=False)
    apex_guides(ax, sym, asym)
    clean_geometry_axis(ax, show_y=True)
    overlay_legend(ax, "Best symmetric")
    save(fig, "right_option_b_configuration_overlay")


def draw_option_c():
    fig, ax = plt.subplots(figsize=(2.12, 2.62))
    fig.subplots_adjust(left=0.25, right=0.98, bottom=0.075, top=0.79)
    asym = draw_colored_set(ax, ASYMMETRIC)
    mirror = draw_dashed_set(ax, mirror=True)
    draw_colored_set(ax, ASYMMETRIC, fill=False)
    apex_guides(ax, mirror, asym)
    clean_geometry_axis(ax, show_y=True)
    overlay_legend(ax, "Its reflection")
    save(fig, "right_option_c_mirror_overlay")


def main():
    draw_combined_figure()
    print(OUT / "kakeya_needle_combined.eps")
    print(OUT / "kakeya_needle_combined.png")


if __name__ == "__main__":
    main()
