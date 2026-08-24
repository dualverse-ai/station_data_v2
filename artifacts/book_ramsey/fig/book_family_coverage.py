#!/usr/bin/env python3
"""Render a six-row bitmap ledger for book-Ramsey coverage at 1 <= n <= 200."""

from __future__ import annotations

import json
import math
import os
import tempfile
from pathlib import Path

os.environ.setdefault("MPLCONFIGDIR", os.path.join(tempfile.gettempdir(), "book_ramsey_bitmap_mplconfig"))

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Patch, Rectangle
from matplotlib.legend_handler import HandlerTuple
import numpy as np
from PIL import Image


HERE = Path(__file__).resolve().parent
OUT = HERE / "book_family_coverage"

INK = "#24292E"
MID_INK = "#5E666D"
GRID = "#D9DDE1"
EMPTY_A = "#F5F6F7"
EMPTY_B = "#EFF1F3"
PRIOR = "#536A82"

CONFERENCE = "#2C61B4"
CONFERENCE_LIGHT = "#B8C7E4"
DOUBLED = "#16856B"
DOUBLED_LIGHT = "#ADD8CB"
YAMADA = "#D56316"
YAMADA_LIGHT = "#EDC29F"


def is_prime(value: int) -> bool:
    if value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    return all(value % divisor for divisor in range(3, math.isqrt(value) + 1, 2))


def is_prime_power(value: int) -> bool:
    if value < 2:
        return False
    if is_prime(value):
        return True
    for prime in range(2, math.isqrt(value) + 1):
        if not is_prime(prime):
            continue
        remainder = value
        while remainder % prime == 0:
            remainder //= prime
        if remainder == 1:
            return True
    return False


def coverage_sets() -> dict[str, set[int]]:
    # L + H in the companion notebook ledger: n <= 21 plus the finite
    # AI-guided search witnesses in Turturean's progress report.
    heuristic = {
        22, 23, 24, 26, 28, 29, 30, 32, 34, 36, 38, 39,
        40, 42, 43, 44, 46, 47, 48, 50, 52, 54, 56,
    }
    finite = set(range(1, 22)) | heuristic

    paley = {
        n for n in range(1, 201)
        if (2 * n - 1) % 4 == 1 and is_prime_power(2 * n - 1)
    }
    # The supplied Turturean summary states the Szekeres source for prime
    # q = 4n - 1 with q == 3 (mod 8).
    szekeres = {
        n for n in range(1, 201)
        if (4 * n - 1) % 8 == 3 and is_prime(4 * n - 1)
    }
    conference = {
        n for n in range(1, 201)
        if ((n - 1) % 4 == 1 and is_prime_power(n - 1)) or n - 1 in {45, 65}
    }
    doubled = {
        n for n in range(1, 201)
        if 2 * n - 1 > 3
        and (2 * n - 1) % 8 == 3
        and is_prime_power(2 * n - 1)
    }
    yamada_pott = {
        (q * q - q + 2) // 4
        for q in range(7, 100)
        if is_prime_power(q)
        and q % 4 == 3
        and (q * q - q + 2) // 4 <= 200
    }

    prior = finite | paley | szekeres
    assert len(prior & set(range(1, 200))) == 103
    assert conference - prior == {
        62, 66, 74, 82, 90, 98, 102, 110, 114, 122,
        126, 138, 150, 158, 170, 174, 182, 194, 198,
    }
    assert doubled - (prior | conference) == {70, 106, 142, 154, 166, 190}
    assert yamada_pott - (prior | conference | doubled) == {86, 127, 176}

    return {
        "finite": finite,
        "paley": paley,
        "szekeres": szekeres,
        "conference": conference,
        "doubled": doubled,
        "yamada_pott": yamada_pott,
    }


def main() -> None:
    OUT.parent.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update(
        {
            "font.family": "sans-serif",
            "font.sans-serif": ["DejaVu Sans"],
            "mathtext.fontset": "dejavusans",
            "font.size": 8.0,
            "axes.labelsize": 9.0,
            "axes.labelweight": "bold",
            "xtick.labelsize": 7.2,
            "ytick.labelsize": 8.1,
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

    sets = coverage_sets()
    prior = sets["finite"] | sets["paley"] | sets["szekeres"]
    # Every Station row uses the same baseline: absence from all first three
    # rows means that the parameter was previously open.
    station_before = {key: prior for key in ("conference", "doubled", "yamada_pott")}
    rows = [
        (
            "Finite examples",
            "",
            "finite", 5.35, PRIOR, PRIOR, True,
        ),
        ("Paley family", "Wesley (2026)", "paley", 4.35, PRIOR, PRIOR, True),
        (
            "Legendre family",
            "Turturean (2026)",
            "szekeres", 3.35, PRIOR, PRIOR, True,
        ),
        ("Conference family", "Station (2026)", "conference", 1.95, CONFERENCE, CONFERENCE_LIGHT, False),
        ("Doubled Legendre family", "Station (2026)", "doubled", 0.95, DOUBLED, DOUBLED_LIGHT, False),
        ("Yamada–Pott family", "Station (2026)", "yamada_pott", -0.05, YAMADA, YAMADA_LIGHT, False),
    ]

    fig, ax = plt.subplots(figsize=(9.1, 2.85), dpi=300)
    fig.subplots_adjust(left=0.275, right=0.992, top=0.975, bottom=0.265)

    row_height = 0.66
    for label, attribution, key, y, dark, light, is_prior_row in rows:
        values = sets[key]
        for n in range(1, 201):
            background = EMPTY_A if ((n - 1) // 10) % 2 == 0 else EMPTY_B
            face = background
            if n in values:
                if is_prior_row:
                    face = dark
                else:
                    face = light if n in station_before[key] else dark
            ax.add_patch(
                Rectangle(
                    (n - 0.47, y - row_height / 2),
                    0.94,
                    row_height,
                    facecolor=face,
                    edgecolor="white",
                    linewidth=0.16,
                    antialiased=False,
                    zorder=2,
                )
            )

    for x in range(20, 201, 20):
        ax.axvline(x + 0.5, color=GRID, linewidth=0.45, zorder=0)

    ax.axhline(2.65, color="#BFC5CA", linewidth=0.75, zorder=1)
    ax.set_yticks([])
    for label, attribution, key, y, dark, light, is_prior_row in rows:
        label_color = INK if is_prior_row else dark
        ax.text(
            -3.0,
            y,
            f"{label}\n{attribution}" if attribution else label,
            ha="right",
            va="center",
            color=label_color,
            fontsize=7.25,
            linespacing=1.34,
            clip_on=False,
        )

    ax.set_xlim(0.5, 200.5)
    ax.set_ylim(-0.62, 5.92)
    ax.set_xticks([1] + list(range(20, 201, 20)))
    ax.set_xlabel(r"Ramsey parameter $n$", labelpad=6)
    ax.tick_params(axis="x", length=2.5, width=0.55, pad=3)
    for spine in ax.spines.values():
        spine.set_visible(False)

    handles = [
        (
            Patch(facecolor=CONFERENCE_LIGHT, edgecolor="none"),
            Patch(facecolor=DOUBLED_LIGHT, edgecolor="none"),
            Patch(facecolor=YAMADA_LIGHT, edgecolor="none"),
        ),
        (
            Patch(facecolor=CONFERENCE, edgecolor="none"),
            Patch(facecolor=DOUBLED, edgecolor="none"),
            Patch(facecolor=YAMADA, edgecolor="none"),
        ),
    ]
    fig.legend(
        handles=handles,
        labels=[
            "Already solved in previous literature",
            "Newly solved by Station",
        ],
        handler_map={tuple: HandlerTuple(ndivide=None, pad=0.12)},
        loc="lower center",
        bbox_to_anchor=(0.635, 0.015),
        ncol=2,
        frameon=False,
        fontsize=8.0,
        handlelength=2.65,
        handleheight=0.85,
        handletextpad=0.7,
        columnspacing=2.5,
        borderpad=0,
    )

    fig.savefig(OUT.with_suffix(".png"), dpi=300)
    fig.savefig(OUT.with_suffix(".pdf"))

    saved = np.asarray(Image.open(OUT.with_suffix(".png")).convert("RGB"))
    height, width = saved.shape[:2]
    content = np.any(saved < 248, axis=2)
    ys, xs = np.where(content)
    plot_left = ax.transData.transform((0.5, 0))[0]
    plot_right = ax.transData.transform((200.5, 0))[0]
    within_group_gap = abs(
        ax.transData.transform((0, 5.35 - row_height / 2))[1]
        - ax.transData.transform((0, 4.35 + row_height / 2))[1]
    )
    between_group_gap = abs(
        ax.transData.transform((0, 3.35 - row_height / 2))[1]
        - ax.transData.transform((0, 1.95 + row_height / 2))[1]
    )
    metrics = {
        "saved_png_pixels": [int(width), int(height)],
        "approx_pixels_per_parameter_cell": round((plot_right - plot_left) / 200, 2),
        "row_count": 6,
        "parameters_per_row": 200,
        "within_group_row_clearance_pixels": round(within_group_gap, 1),
        "between_group_clearance_pixels": round(between_group_gap, 1),
        "between_group_clearance_percent_of_saved_height": round(
            100 * between_group_gap / height, 2
        ),
        "outer_white_margins_saved_png": {
            "left_px": int(xs.min()),
            "right_px": int(width - 1 - xs.max()),
            "top_px": int(ys.min()),
            "bottom_px": int(height - 1 - ys.max()),
        },
        "coverage_counts_1_to_200": {key: len(value) for key, value in sets.items()},
        "previously_open_resolved": {
            key: sorted(sets[key] - station_before[key])
            for key in ("conference", "doubled", "yamada_pott")
        },
    }
    (HERE / "book_family_coverage_layout.json").write_text(
        json.dumps(metrics, indent=2) + "\n"
    )
    print(json.dumps(metrics, indent=2))
    plt.close(fig)


if __name__ == "__main__":
    main()
