#!/usr/bin/env python3
"""Render the history of the published interval for the minimum-overlap constant."""

import json
import os
import tempfile
from pathlib import Path

os.environ.setdefault("MPLCONFIGDIR", os.path.join(tempfile.gettempdir(), "autocorr_gap_history_mplconfig"))

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
import numpy as np
from PIL import Image


HERE = Path(__file__).resolve().parent
DATA_PATH = HERE / "figdata.json"
OUTPUT_DIR = HERE
STEM = OUTPUT_DIR / "autocorr_gap_history"

# Palette and typography follow the finalized Station paper figures.  Historical
# lower and upper endpoints use the established orange/teal pairing; the
# Station result uses the paper's dark emphasis blue.
INK = "#22262A"
MID_INK = "#62686D"
LIGHT_INK = "#AEB4BA"
GRID = "#D4D6D8"
ORANGE = "#D95F02"
ORANGE_DARK = "#8A3D01"
ORANGE_LIGHT = "#E6A373"
TEAL = "#1B9E77"
TEAL_DARK = "#0F5B45"
TEAL_LIGHT = "#71C4B0"
BLUE = "#2C61B4"
NAVY = "#183664"

plt.rcParams.update(
    {
        "font.family": "sans-serif",
        "font.sans-serif": ["DejaVu Sans"],
        "mathtext.fontset": "dejavusans",
        "font.size": 8.0,
        "axes.labelsize": 9.0,
        "axes.labelweight": "bold",
        "xtick.labelsize": 7.2,
        "ytick.labelsize": 7.6,
        "axes.linewidth": 0.72,
        "axes.edgecolor": INK,
        "xtick.color": INK,
        "ytick.color": INK,
        "xtick.direction": "out",
        "xtick.major.size": 3.0,
        "xtick.major.width": 0.65,
        "figure.facecolor": "white",
        "savefig.facecolor": "white",
        "savefig.bbox": "tight",
        "savefig.pad_inches": 0.025,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    }
)


def load_rows():
    with DATA_PATH.open() as handle:
        payload = json.load(handle)
    rows = payload["rows"]
    assert len(rows) == 4
    for row in rows:
        assert row["lower"] < row["upper"]
    return rows


def endpoint_label(source, value):
    return f"{source}\n{value:.6f}"


def render():
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    rows = load_rows()
    y = np.arange(len(rows))[::-1]

    # Full journal-page width, but deliberately shallow: this is a single idea,
    # not a multi-panel technical plot.
    fig, ax = plt.subplots(figsize=(7.4, 2.38), dpi=300)
    fig.subplots_adjust(left=0.215, right=0.985, top=0.955, bottom=0.275)

    lower = np.asarray([row["lower"] for row in rows])
    upper = np.asarray([row["upper"] for row in rows])

    # Endpoint trajectories make the history visible at a glance.  The small
    # 2016--2026 moves are intentionally drawn on the same linear scale as the
    # Station jump.
    ax.plot(lower, y, color=ORANGE_LIGHT, linewidth=0.72,
            linestyle=(0, (2, 2)), zorder=1)
    ax.plot(upper, y, color=TEAL_LIGHT, linewidth=0.72,
            linestyle=(0, (2, 2)), zorder=1)
    for index, (row, yy) in enumerate(zip(rows, y)):
        is_station = index == len(rows) - 1
        line_color = BLUE if is_station else LIGHT_INK
        ax.plot(
            [row["lower"], row["upper"]],
            [yy, yy],
            color=line_color,
            linewidth=6.2 if is_station else 5.0,
            solid_capstyle="butt",
            zorder=3,
        )

        ax.scatter(
            [row["lower"]], [yy], marker="o", s=29,
            facecolor=ORANGE, edgecolor=ORANGE_DARK,
            linewidth=0.65, zorder=5, clip_on=False,
        )
        ax.scatter(
            [row["upper"]], [yy], marker="s", s=30,
            facecolor=TEAL, edgecolor=TEAL_DARK,
            linewidth=0.65, zorder=5, clip_on=False,
        )

        # Endpoint sources and values sit above the bar and stay tied to their
        # endpoints; values never exceed six displayed decimal places.
        ax.annotate(
            endpoint_label(row["lower_source"], row["lower"]),
            xy=(row["lower"], yy), xytext=(-4, 6.8),
            textcoords="offset points", ha="right", va="bottom",
            fontsize=6.55, linespacing=1.03,
            color=ORANGE_DARK,
            clip_on=False,
        )
        ax.annotate(
            endpoint_label(row["upper_source"], row["upper"]),
            xy=(row["upper"], yy), xytext=(4, 6.8),
            textcoords="offset points", ha="left", va="bottom",
            fontsize=6.55, linespacing=1.03, color=TEAL_DARK,
            clip_on=False,
        )

    labels = [f"{row['stage']}\n{row['display_year']}" for row in rows]
    ax.set_yticks(y, labels)
    ax.tick_params(axis="y", length=0, pad=10)
    for idx, tick in enumerate(ax.get_yticklabels()):
        tick.set_horizontalalignment("right")
        if idx == len(rows) - 1:
            tick.set_color(BLUE)
            tick.set_fontweight("bold")

    ax.set_xlim(0.37886, 0.381035)
    ax.set_ylim(-0.31, 3.50)
    ticks = [0.3790, 0.3794, 0.3798, 0.3802, 0.3806, 0.3810]
    ax.set_xticks(ticks, [f"{value:.4f}" for value in ticks])
    ax.set_xlabel(r"value of $\mu$", labelpad=6)
    ax.grid(axis="x", color=GRID, linestyle=":", linewidth=0.48, zorder=0)
    ax.set_axisbelow(True)
    for side in ("left", "right", "top"):
        ax.spines[side].set_visible(False)

    # A compact bottom key explains the visual grammar without requiring a
    # title or in-figure prose block.
    handles = [
        Line2D([], [], linestyle="none", marker="o", markersize=4.5,
               markerfacecolor=ORANGE, markeredgecolor=ORANGE_DARK,
               markeredgewidth=0.6, label="lower bound"),
        Line2D([], [], linestyle="none", marker="s", markersize=4.4,
               markerfacecolor=TEAL, markeredgecolor=TEAL_DARK,
               markeredgewidth=0.6, label="upper bound"),
    ]
    fig.legend(
        handles=handles, loc="lower center", bbox_to_anchor=(0.62, 0.018),
        ncol=2, frameon=False, fontsize=7.0,
        handlelength=1.5, handletextpad=0.55, columnspacing=1.85,
        borderpad=0,
    )

    # Quantitative layout audit, including the vertical middle band requested
    # for candidate comparison.  The band between rows 2 and 3 is measured in
    # pixels and as a fraction of the drawable plot height.
    fig.canvas.draw()
    canvas_w, canvas_h = fig.canvas.get_width_height()
    ax_box = ax.get_window_extent()
    row_px = [ax.transData.transform((0, yy))[1] for yy in y]
    bar_half_height_px = (5.0 / 72.0) * fig.dpi / 2.0
    middle_clear_px = row_px[1] - row_px[2] - 2.0 * bar_half_height_px
    middle_center_spacing_px = row_px[1] - row_px[2]
    middle_pct_canvas = 100.0 * middle_clear_px / canvas_h
    middle_pct_axes = 100.0 * middle_clear_px / ax_box.height

    # A content bounding box based on non-white pixels gives an objective outer
    # whitespace check for the PNG preview.
    fig.canvas.draw()
    rgb = np.asarray(fig.canvas.buffer_rgba())[..., :3]
    content = np.any(rgb < 250, axis=2)
    ys, xs = np.nonzero(content)
    bbox = (int(xs.min()), int(ys.min()), int(xs.max()), int(ys.max()))
    content_fraction = 100.0 * content.mean()
    outer_white = {
        "left_px": bbox[0],
        "right_px": canvas_w - 1 - bbox[2],
        "top_px": bbox[1],
        "bottom_px": canvas_h - 1 - bbox[3],
    }

    for extension, kwargs in (
        ("png", {"dpi": 300}),
        ("pdf", {}),
        ("eps", {}),
    ):
        path = Path(f"{STEM}.{extension}")
        fig.savefig(path, format=extension, **kwargs)
        print(f"wrote {path} ({path.stat().st_size:,} bytes)")

    saved_rgb = np.asarray(Image.open(f"{STEM}.png").convert("RGB"))
    saved_h, saved_w = saved_rgb.shape[:2]
    saved_content = np.any(saved_rgb < 250, axis=2)
    saved_ys, saved_xs = np.nonzero(saved_content)
    saved_bbox = (
        int(saved_xs.min()), int(saved_ys.min()),
        int(saved_xs.max()), int(saved_ys.max()),
    )

    metrics = {
        "canvas_pixels_before_tight_crop": [canvas_w, canvas_h],
        "saved_png_pixels": [saved_w, saved_h],
        "plot_box_pixels": [round(ax_box.width, 1), round(ax_box.height, 1)],
        "middle_row_center_spacing_pixels": round(middle_center_spacing_px, 1),
        "middle_row_clearance_pixels": round(middle_clear_px, 1),
        "middle_row_clearance_percent_of_canvas_height": round(middle_pct_canvas, 2),
        "middle_row_clearance_percent_of_saved_png_height": round(
            100.0 * middle_clear_px / saved_h, 2
        ),
        "middle_row_clearance_percent_of_plot_height": round(middle_pct_axes, 2),
        "nonwhite_content_fraction_percent": round(content_fraction, 2),
        "outer_white_margins_before_tight_crop": outer_white,
        "outer_white_margins_saved_png": {
            "left_px": saved_bbox[0],
            "right_px": saved_w - 1 - saved_bbox[2],
            "top_px": saved_bbox[1],
            "bottom_px": saved_h - 1 - saved_bbox[3],
        },
    }
    metrics_path = HERE / "layout_metrics.json"
    metrics_path.write_text(json.dumps(metrics, indent=2) + "\n")
    print(json.dumps(metrics, indent=2))
    plt.close(fig)


if __name__ == "__main__":
    render()
