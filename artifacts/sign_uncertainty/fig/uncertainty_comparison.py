#!/usr/bin/env python3
"""Render the sign-uncertainty comparison figure."""

import json
import os
import tempfile
from pathlib import Path

os.environ.setdefault("MPLCONFIGDIR", os.path.join(tempfile.gettempdir(), "uncertainty_figure_mplconfig"))

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import LinearSegmentedColormap
from matplotlib.lines import Line2D
import mpmath as mp
import numpy as np

HERE = Path(__file__).resolve().parent
AE_ROOTS_PATH = HERE / "ae12_roots.json"
STATION_ROOTS_PATH = HERE / "station_k20_roots.json"
CONTINUUM_CERT_PATH = HERE / "cert_k56_serialized.json"
INK = "#22262A"
MID_INK = "#62686D"
ORANGE = "#D95F02"
TEAL = "#1B9E77"
TEAL_DARK = "#08775B"
GOLD = "#B57C00"
BLUE = "#2C61B4"
ZERO = "#92979B"
LEFT_AXIS_LEFT = 0.3726
LEFT_AXIS_RIGHT = 0.985
COEFFICIENT_CMAP = LinearSegmentedColormap.from_list(
    "coefficient_sign", [ORANGE, "#F7F7F5", BLUE]
)

mp.mp.dps = 180


def laguerre_values(max_degree, alpha, t):
    """Return generalized Laguerre values through ``max_degree``."""
    values = [mp.mpf(1)]
    if max_degree == 0:
        return values
    values.append(alpha + 1 - t)
    for n in range(1, max_degree):
        values.append(
            ((2 * n + 1 + alpha - t) * values[n] - (n + alpha) * values[n - 1])
            / (n + 1)
        )
    return values


def basis_and_derivatives(degrees, t):
    values = laguerre_values(max(degrees), mp.mpf("-0.5"), t)
    derivatives = laguerre_values(max(degrees) - 1, mp.mpf("0.5"), t)
    return (
        [values[n] for n in degrees],
        [mp.mpf(0) if n == 0 else -derivatives[n - 1] for n in degrees],
    )


def reconstruct_double_root(roots):
    roots = [mp.mpf(str(value)) for value in roots]
    degrees = list(range(0, 4 * len(roots) + 4, 2))
    size = len(degrees)
    matrix = mp.matrix(size, size)
    rhs = mp.matrix(size, 1)
    rhs[1] = 1

    values, derivatives = basis_and_derivatives(degrees, mp.mpf(0))
    for j in range(size):
        matrix[0, j] = values[j]
        matrix[1, j] = derivatives[j]
    for i, root in enumerate(roots):
        values, derivatives = basis_and_derivatives(degrees, root)
        for j in range(size):
            matrix[2 * i + 2, j] = values[j]
            matrix[2 * i + 3, j] = derivatives[j]
    solution = mp.lu_solve(matrix, rhs)
    return degrees, [solution[j] for j in range(size)]


def eval_polynomial(degrees, coefficients, t):
    values = laguerre_values(max(degrees), mp.mpf("-0.5"), t)
    return mp.fsum(c * values[n] for n, c in zip(degrees, coefficients))


def eval_polynomial_derivative(degrees, coefficients, t):
    _, derivatives = basis_and_derivatives(degrees, t)
    return mp.fsum(c * value for c, value in zip(coefficients, derivatives))


def load_witnesses():
    ae_roots = json.loads(AE_ROOTS_PATH.read_text(encoding="utf-8"))
    station_roots = json.loads(STATION_ROOTS_PATH.read_text(encoding="utf-8"))
    certificate = json.loads(CONTINUUM_CERT_PATH.read_text(encoding="utf-8"))

    ae_degrees, ae_coefficients = reconstruct_double_root(ae_roots)
    station_degrees, station_coefficients = reconstruct_double_root(station_roots)
    continuum_degrees = [int(n) for n in certificate["basis_degrees"]]
    continuum_coefficients = [
        mp.mpf(value) for value in certificate["laguerre_coefficients_rational"]
    ]

    for degrees, coefficients in (
        (ae_degrees, ae_coefficients),
        (station_degrees, station_coefficients),
        (continuum_degrees, continuum_coefficients),
    ):
        assert abs(eval_polynomial(degrees, coefficients, mp.mpf(0))) < mp.mpf("1e-90")
        assert abs(eval_polynomial_derivative(degrees, coefficients, mp.mpf(0)) - 1) < mp.mpf("1e-90")
    for roots, degrees, coefficients in (
        (ae_roots, ae_degrees, ae_coefficients),
        (station_roots, station_degrees, station_coefficients),
    ):
        for root in roots:
            root_mp = mp.mpf(str(root))
            assert abs(eval_polynomial(degrees, coefficients, root_mp)) < mp.mpf("1e-120")
            assert abs(eval_polynomial_derivative(degrees, coefficients, root_mp)) < mp.mpf("1e-120")
    assert abs(float(certificate["candidate_A"]) - 0.3089) < 1e-15

    return {
        "AlphaEvolve": {
            "score": 0.321591,
            "degrees": ae_degrees,
            "coefficients": ae_coefficients,
            "roots": ae_roots,
        },
        "Station evaluator": {
            "score": 0.3153090099692479,
            "degrees": station_degrees,
            "coefficients": station_coefficients,
            "roots": station_roots,
        },
        "Station theorem": {
            "score": 0.3089,
            "degrees": continuum_degrees,
            "coefficients": continuum_coefficients,
            "roots": [],
        },
    }

plt.rcParams.update(
    {
        "font.family": "sans-serif",
        "font.sans-serif": ["DejaVu Sans"],
        "mathtext.fontset": "dejavusans",
        "font.size": 7.4,
        "axes.labelsize": 7.9,
        "axes.labelweight": "bold",
        "axes.titlesize": 7.2,
        "xtick.labelsize": 6.7,
        "ytick.labelsize": 6.7,
        "axes.linewidth": 0.65,
        "axes.edgecolor": INK,
        "xtick.color": INK,
        "ytick.color": INK,
        "xtick.direction": "out",
        "ytick.direction": "out",
        "xtick.major.size": 2.6,
        "ytick.major.size": 2.6,
        "xtick.major.width": 0.6,
        "ytick.major.width": 0.6,
        "figure.facecolor": "white",
        "savefig.facecolor": "white",
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    }
)


BOUND_RECORDS = [
    ("Pre-AlphaEvolve\nLiterature", 0.32831, ORANGE, "0.32831"),
    ("AlphaEvolve", 0.321591, TEAL, "0.321591"),
    ("Optimum in double-root\nLaguerre family", 0.3153090099692479, TEAL_DARK, "0.315305–0.315309"),
    ("Announced human\nresults", 0.3102, GOLD, "0.3102"),
    ("Station", 0.3089, BLUE, "0.3089"),
]

CURVE_ROWS = [
    ("AlphaEvolve", "AlphaEvolve", TEAL, "o", (-0.04, 0.05), [-0.04, 0, 0.04]),
    (
        "Station double-root construction",
        "Station evaluator",
        TEAL_DARK,
        "o",
        (-0.025, 0.025),
        [-0.02, 0, 0.02],
    ),
    (
        "Station",
        "Station theorem",
        BLUE,
        None,
        (-0.012, 0.012),
        [-0.01, 0, 0.01],
    ),
]

PRODUCT_LABELS = {
    "AlphaEvolve": r"$A(f)A(\widehat f)=0.321591$",
    "Station evaluator": r"$A(f)A(\widehat f)=0.315309$",
    "Station theorem": r"$A(f)A(\widehat f)\leq 0.3089$",
}


def clean_axis(ax, left=True, bottom=True):
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.spines["left"].set_visible(left)
    ax.spines["bottom"].set_visible(bottom)


def draw_bounds(ax):
    origin = 0.305
    ypos = np.arange(len(BOUND_RECORDS))[::-1]
    for y, (label, value, color, shown) in zip(ypos, BOUND_RECORDS):
        ax.barh(
            y,
            value - origin,
            left=origin,
            height=0.48,
            color=color,
            edgecolor="none",
            linewidth=0,
        )
        ax.annotate(
            shown,
            xy=(value, y),
            xytext=(3.5, 0),
            textcoords="offset points",
            ha="left",
            va="center",
            color=INK,
            fontsize=6.6 if "–" in shown else 6.7,
            clip_on=False,
        )

    ax.set_yticks(ypos, [record[0] for record in BOUND_RECORDS])
    # The extra right margin keeps the longest value label clear of the
    # neighboring panel's ordinate labels without opening the panel gutter.
    ax.set_xlim(origin, 0.3360)
    ax.set_ylim(-0.64, 4.64)
    ax.set_xticks([0.305, 0.310, 0.315, 0.320, 0.325, 0.330])
    ax.set_xlabel("upper bound on $C$ (lower is better)", labelpad=4)
    ax.xaxis.label.set_fontsize(7.9)
    ax.xaxis.set_label_coords(
        (0.5 - LEFT_AXIS_LEFT) / (LEFT_AXIS_RIGHT - LEFT_AXIS_LEFT), -0.14
    )
    ax.tick_params(axis="y", length=0, pad=4.5)
    clean_axis(ax, left=False, bottom=True)
    ax.spines["bottom"].set_visible(False)
    ax.plot(
        [origin, 0.331],
        [0, 0],
        transform=ax.get_xaxis_transform(),
        color=INK,
        linewidth=0.65,
        clip_on=False,
        zorder=4,
    )

    # Honest truncation marker: a zero-based bar chart would make the relevant
    # differences visually disappear.
    slash = dict(transform=ax.transAxes, color=INK, clip_on=False, linewidth=0.68)
    ax.plot((-0.012, 0.003), (-0.016, 0.016), **slash)
    ax.plot((0.004, 0.019), (-0.016, 0.016), **slash)


def curve_values(witness, x_values):
    return np.asarray(
        [
            float(
                -eval_polynomial(
                    witness["degrees"],
                    witness["coefficients"],
                    2 * mp.pi * mp.mpf(str(x)) ** 2,
                )
            )
            for x in x_values
        ]
    )


def draw_curve(ax, title, witness, color, marker, ylim, yticks, show_x):
    x_values = np.linspace(0.54, 1.0, 1150)
    ax.axhline(0, color=ZERO, linewidth=0.52, zorder=1)
    ax.plot(x_values, curve_values(witness, x_values), color=color, linewidth=1.22, zorder=3)

    if marker is not None:
        radii = [
            float(mp.sqrt(mp.mpf(str(root)) / (2 * mp.pi)))
            for root in witness["roots"]
        ]
        radii = [radius for radius in radii if x_values[0] <= radius <= x_values[-1]]
        ax.scatter(
            radii,
            np.zeros(len(radii)),
            marker=marker,
            s=11.5,
            facecolors="white",
            edgecolors=color,
            linewidths=0.72,
            zorder=5,
        )

    # Titles sit in dedicated whitespace above the axes, never over the data.
    ax.set_title(title, loc="left", pad=2.2, color=INK, fontweight="normal")
    ax.set_xlim(0.54, 1.0)
    ax.set_ylim(*ylim)
    ax.set_yticks(yticks)
    ax.tick_params(axis="y", pad=2)
    clean_axis(ax, left=True, bottom=show_x)
    if show_x:
        ax.set_xticks([0.55, 0.65, 0.75, 0.85, 0.95])
        ax.set_xlabel(r"radius $x$", labelpad=3.5)
    else:
        ax.tick_params(axis="x", bottom=False, labelbottom=False)


def add_header_key(panel):
    circle = Line2D(
        [], [], linestyle="none", marker="o", markersize=3.8,
        markerfacecolor="white", markeredgecolor=MID_INK, markeredgewidth=0.7,
    )
    panel.text(
        0.08,
        0.935,
        r"curve: $-P(2\pi x^2)$",
        ha="left",
        va="bottom",
        fontsize=6.6,
        color=MID_INK,
    )
    panel.legend(
        handles=[circle],
        labels=["prescribed double roots"],
        loc="lower right",
        bbox_to_anchor=(0.985, 0.925),
        bbox_transform=panel.transSubfigure,
        frameon=False,
        fontsize=6.6,
        handletextpad=0.35,
        borderpad=0,
    )


def save(fig, stem):
    fig.canvas.draw()
    width_px, height_px = fig.canvas.get_width_height()
    left_ax = fig.axes[0]
    first_right = fig.axes[1]
    gutter_px = first_right.get_window_extent().x0 - left_ax.get_window_extent().x1
    renderer = fig.canvas.get_renderer()
    value_right = max(text.get_window_extent(renderer).x1 for text in left_ax.texts)
    tick_left = min(
        label.get_window_extent(renderer).x0
        for label in first_right.get_yticklabels()
        if label.get_visible() and label.get_text()
    )
    drawn_axis_end = left_ax.transData.transform((0.331, 0))[0]
    axis_to_tick_clearance = tick_left - drawn_axis_end
    left_panel, right_panel = fig._uncertainty_panels
    left_width = left_panel.bbox.width
    right_width = right_panel.bbox.width
    content_clearance = tick_left - value_right
    xlabel_width = left_ax.xaxis.label.get_window_extent(renderer).width
    xlabel_center = left_ax.xaxis.label.get_window_extent(renderer).x0 + 0.5 * xlabel_width
    panel_center = left_panel.bbox.x0 + 0.5 * left_width
    xlabel_center_error = xlabel_center - panel_center
    content_boxes = [
        label.get_window_extent(renderer)
        for label in (
            list(left_ax.get_yticklabels())
            + list(left_ax.get_xticklabels())
            + [left_ax.xaxis.label]
            + list(left_ax.texts)
        )
        if label.get_visible() and label.get_text()
    ]
    content_boxes.extend(
        patch.get_window_extent(renderer)
        for patch in left_ax.patches
        if patch.get_visible()
    )
    content_boxes.extend(
        line.get_window_extent(renderer)
        for line in left_ax.lines
        if line.get_visible()
    )
    content_left = min(box.x0 for box in content_boxes)
    content_right = max(box.x1 for box in content_boxes)
    left_margin = content_left - left_panel.bbox.x0
    right_margin = left_panel.bbox.x1 - content_right
    content_center_error = 0.5 * (content_left + content_right) - panel_center
    print(
        f"{stem}: canvas={width_px}x{height_px}px; middle gutter={gutter_px:.1f}px "
        f"({100 * gutter_px / width_px:.2f}% of width); "
        f"value-to-tick clearance={content_clearance:.1f}px; "
        f"axis-to-tick clearance={axis_to_tick_clearance:.1f}px; "
        f"subfigure widths={left_width:.1f}/{right_width:.1f}px "
        f"({100 * left_width / width_px:.2f}%/{100 * right_width / width_px:.2f}%); "
        f"left xlabel={xlabel_width:.1f}px "
        f"({100 * xlabel_width / left_width:.2f}% of its subfigure, "
        f"{100 * xlabel_width / width_px:.2f}% of canvas), "
        f"center error={xlabel_center_error:.1f}px; "
        f"content margins L/R={left_margin:.1f}/{right_margin:.1f}px; "
        f"whole-chart center error={content_center_error:.1f}px"
    )
    for suffix, kwargs in (("png", {"dpi": 300}), ("pdf", {}), ("eps", {})):
        path = HERE / f"{stem}.{suffix}"
        fig.savefig(path, format=suffix, **kwargs)
        print(f"wrote {path} ({path.stat().st_size:,} bytes)")
    plt.close(fig)


def render_figure(witnesses):
    fig = plt.figure(figsize=(7.4, 2.95), dpi=300)
    left_panel, right_panel = fig.subfigures(1, 2, width_ratios=(1, 1), wspace=0)
    fig._uncertainty_panels = (left_panel, right_panel)
    left_grid = left_panel.add_gridspec(
        1,
        1,
        left=LEFT_AXIS_LEFT,
        right=LEFT_AXIS_RIGHT,
        bottom=0.205,
        top=0.875,
    )
    right_grid = right_panel.add_gridspec(
        3, 1, left=0.08, right=0.985, bottom=0.205, top=0.875, hspace=0.39
    )
    bound_ax = left_panel.add_subplot(left_grid[0, 0])
    curve_axes = [right_panel.add_subplot(right_grid[i, 0]) for i in range(3)]
    draw_bounds(bound_ax)
    for i, (ax, row) in enumerate(zip(curve_axes, CURVE_ROWS)):
        title, key, color, marker, ylim, yticks = row
        draw_curve(ax, title, witnesses[key], color, marker, ylim, yticks, i == 2)
        ax.text(
            0.995,
            1.025,
            PRODUCT_LABELS[key],
            transform=ax.transAxes,
            ha="right",
            va="bottom",
            fontsize=6.6,
            color=MID_INK,
        )
    add_header_key(right_panel)
    save(fig, "uncertainty_comparison")


def coefficient_spectrum(ax, coefficients, show_x):
    coeff = np.asarray([float(value) for value in coefficients])
    modes = np.arange(len(coeff))
    colors = np.where(coeff >= 0, BLUE, ORANGE)
    ax.axhline(0, color=ZERO, linewidth=0.48, zorder=1)
    ax.vlines(modes, 0, coeff, colors=colors, linewidth=0.62, zorder=2)
    ax.scatter(modes, coeff, c=colors, s=2.5, edgecolors="none", zorder=3)
    ax.set_xlim(-2, 115)
    ax.set_ylim(-0.12, 0.09)
    ax.set_yticks([-0.10, 0, 0.08])
    ax.tick_params(axis="y", labelsize=6.5, pad=1.5)
    clean_axis(ax, left=True, bottom=show_x)
    if show_x:
        ax.set_xticks([0, 50, 100])
        ax.set_xlabel("mode index $j$", labelpad=3)
    else:
        ax.tick_params(axis="x", bottom=False, labelbottom=False)


def enhanced(witnesses):
    fig = plt.figure(figsize=(7.4, 3.25), dpi=300)
    left_panel, right_panel = fig.subfigures(1, 2, width_ratios=(1, 1), wspace=0)
    fig._uncertainty_panels = (left_panel, right_panel)
    left_grid = left_panel.add_gridspec(
        1, 1, left=0.46, right=0.985, bottom=0.175, top=0.875
    )
    right_grid = right_panel.add_gridspec(
        3,
        2,
        left=0.08,
        right=0.985,
        bottom=0.175,
        top=0.875,
        width_ratios=(2.55, 1.0),
        hspace=0.39,
        wspace=0.24,
    )
    bound_ax = left_panel.add_subplot(left_grid[0, 0])
    curve_axes = []
    spectrum_axes = []
    for i in range(3):
        curve_axes.append(right_panel.add_subplot(right_grid[i, 0]))
        spectrum_axes.append(right_panel.add_subplot(right_grid[i, 1]))

    draw_bounds(bound_ax)
    for i, (curve_ax, spectrum_ax, row) in enumerate(zip(curve_axes, spectrum_axes, CURVE_ROWS)):
        title, key, color, marker, ylim, yticks = row
        modes = len(witnesses[key]["coefficients"])
        draw_curve(
            curve_ax,
            title,
            witnesses[key],
            color,
            marker,
            ylim,
            yticks,
            i == 2,
        )
        coefficient_spectrum(
            spectrum_ax, witnesses[key]["coefficients"], show_x=(i == 2)
        )
        spectrum_ax.set_title(
            f"{modes} modes", loc="right", pad=2.2, color=INK, fontweight="normal"
        )

    # Column headers and the root key occupy separate horizontal zones inside
    # the equal-width right subfigure.
    right_panel.text(
        0.08,
        0.935,
        r"curve: $-P(2\pi x^2)$",
        ha="left",
        va="bottom",
        fontsize=6.5,
        color=MID_INK,
    )
    right_panel.text(
        0.875,
        0.925,
        "Laguerre coefficients\nblue $+$ · orange $-$",
        ha="center",
        va="bottom",
        fontsize=6.5,
        color=MID_INK,
        linespacing=0.95,
    )
    circle = Line2D([], [], linestyle="none", marker="o", markersize=3.4,
                    markerfacecolor="white", markeredgecolor=MID_INK,
                    markeredgewidth=0.65)
    right_panel.legend(
        handles=[circle],
        labels=["double roots"],
        loc="lower right",
        bbox_to_anchor=(0.62, 0.925),
        bbox_transform=right_panel.transSubfigure,
        frameon=False,
        fontsize=6.5,
        handletextpad=0.25,
        borderpad=0,
    )
    save(fig, "uncertainty_comparison_spectrum")


def main():
    witnesses = load_witnesses()
    render_figure(witnesses)


if __name__ == "__main__":
    main()
