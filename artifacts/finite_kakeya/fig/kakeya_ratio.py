#!/usr/bin/env python3
"""Generate the finite-Kakeya comparison figure beside this script."""

import json
import os
import tempfile

os.environ.setdefault("MPLCONFIGDIR", os.path.join(tempfile.gettempdir(), "finite_kakeya_figure_mplconfig"))

import matplotlib

matplotlib.use("Agg")  # headless: no display needed
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D

# ---------------------------------------------------------------------------
# Palette recovered from arXiv:2511.06309 content streams
# ---------------------------------------------------------------------------
# Monochrome blue ramp, lightest -> darkest, as used for the reference's grouped
# bar charts (Figures 8 and 13 of the reference).
BLUE_RAMP = [
    "#D1D9EF",
    "#BDCAEA",
    "#A9BBE5",
    "#8DAADF",
    "#719ADA",  # the reference's primary line/marker blue
    "#4E7DC7",
    "#2C61B4",  # the reference's darkest emphasis blue
]

NAVY_EDGE = "#183664"  # marker/bar edge colour in the reference
GRID_GREY = "#CCCCCC"

# Series roles. The three curves run within a line width of each other at most
# cells, so lightness alone does not separate them: the two reference curves take
# distinct hues (ColorBrewer Dark2 orange and teal, safe against each other and
# against blue under colour-vision deficiency) and Station keeps the reference
# blue. Every line is solid, so distinct marker shapes carry the encoding a second
# time and the curves stay separable in greyscale.
C_LIT = "#D95F02"  # literature  : orange
C_AE = "#1B9E77"  # AlphaEvolve : teal
C_ST = BLUE_RAMP[6]  # Station     : the reference's emphasis blue
C_LIT_EDGE = "#8A3D01"
C_AE_EDGE = "#0F5B45"

# ---------------------------------------------------------------------------
# Global rcParams
# ---------------------------------------------------------------------------
plt.rcParams.update(
    {
        "text.usetex": False,  # mathtext only, so no TeX install is required
        "font.family": "sans-serif",
        "font.sans-serif": ["DejaVu Sans"],
        "mathtext.fontset": "dejavusans",
        "font.size": 9.5,
        "axes.labelsize": 10.5,
        "axes.labelweight": "bold",  # reference uses bold axis labels
        "axes.titlesize": 10.5,
        "xtick.labelsize": 8.5,
        "ytick.labelsize": 8.5,
        "legend.fontsize": 8.5,
        "axes.linewidth": 0.9,
        "axes.edgecolor": "black",
        "axes.grid": True,
        "axes.axisbelow": True,  # grid beneath the data
        "grid.color": GRID_GREY,
        "grid.linestyle": ":",
        "grid.linewidth": 0.5,
        "xtick.direction": "out",
        "ytick.direction": "out",
        "xtick.major.width": 0.9,
        "ytick.major.width": 0.9,
        "legend.frameon": False,  # no border around the legend
        "legend.borderpad": 0.0,
        "legend.handlelength": 2.2,
        "figure.facecolor": "white",
        "savefig.facecolor": "white",
        "savefig.bbox": "tight",
        "savefig.pad_inches": 0.02,
        "ps.fonttype": 42,  # embed TrueType rather than Type 3 in the EPS
        "pdf.fonttype": 42,
    }
)

HERE = os.path.dirname(os.path.abspath(__file__))
DATA_PATH = os.path.join(HERE, "figdata.json")
OUTPUT_DIR = HERE
DIMS = (3, 4, 5)


def load_data():
    """Load figdata.json and group records by dimension, sorted by p."""
    with open(DATA_PATH) as fh:
        records = json.load(fh)
    by_d = {d: sorted((r for r in records if r["d"] == d), key=lambda r: r["p"]) for d in DIMS}
    return records, by_d


def save(fig, stem):
    """Write PDF and EPS vector deliverables plus a 150 dpi PNG preview."""
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    pdf_path = os.path.join(OUTPUT_DIR, stem + ".pdf")
    eps_path = os.path.join(OUTPUT_DIR, stem + ".eps")
    png_path = os.path.join(OUTPUT_DIR, stem + ".png")
    fig.savefig(pdf_path, format="pdf")
    fig.savefig(eps_path, format="eps")
    fig.savefig(png_path, format="png", dpi=150)
    plt.close(fig)
    print("wrote {}  ({:,} bytes)".format(pdf_path, os.path.getsize(pdf_path)))
    print("wrote {}  ({:,} bytes)".format(eps_path, os.path.getsize(eps_path)))
    print("wrote {}  ({:,} bytes)".format(png_path, os.path.getsize(png_path)))


def cell_verdict(rec):
    """Return (prior_best, station, points_saved, percent_saved) for one cell.

    Prior best is min(literature, AlphaEvolve): Station is compared against the
    better of BOTH prior curves, never the weaker one.
    """
    prior = min(rec["lit"], rec["ae"])
    saved = prior - rec["station"]
    return prior, rec["station"], saved, 100.0 * saved / prior


# ===========================================================================
# Figure 1 - normalized ratio |K|/B vs p, one panel per dimension
# ===========================================================================
def fig_ratio(by_d):
    """Main figure: |K_p| / B_{p,d} against p, three curves, one panel per d.

    Three judgement calls:

    1. x-axis is *categorical* (evenly spaced prime slots), not logarithmic.
       A log axis was tried first, per the brief's suggestion, but it packs the
       upper primes of the d=3 panel (37, 41, 43, 47, 53) into a few
       millimetres: the tick labels collide and the markers fuse into a blob.
       Even spacing gives every prime a legible slot and every marker room to
       be distinguished, which serves the figure's actual job -- comparing three
       curves cell by cell -- better than metric fidelity in p. All three panels
       are the same width, so the slot pitch differs between panels (the d=3
       panel holds 14 primes and the d=5 panel 4); tick label size is reduced
       where the slots are tight.

    2. Independent y-limits per panel. The ratio bands are disjoint across
       dimensions (~0.76-0.98 at d=3 versus ~0.47-0.60 at d=5), so a shared
       y-scale would compress every curve into a flat sliver. The shared *label*
       on the left carries the common meaning, as the brief requested.

    3. Nested marker sizes (literature largest, Station smallest) so the many
       exact ties stay readable: at a tied cell the reader sees Station's small
       dark dot sitting inside the larger lighter marker, rather than one curve
       silently hiding the others.
    """
    fig, axes = plt.subplots(1, 3, figsize=(7.4, 2.55), layout="constrained")
    fig.get_layout_engine().set(w_pad=0.03, h_pad=0.02, wspace=0.05)

    series = [
        ("Pre-AlphaEvolve literature", "lit_r", C_LIT, C_LIT_EDGE, "-", "^", 6.6),
        ("AlphaEvolve", "ae_r", C_AE, C_AE_EDGE, "-", "s", 5.2),
        ("Station", "station_r", C_ST, NAVY_EDGE, "-", "o", 3.6),
    ]

    for ax, d in zip(axes, DIMS):
        rows = by_d[d]
        ps = [r["p"] for r in rows]
        xs = list(range(len(rows)))  # evenly spaced categorical slots
        for label, key, colour, edge, ls, marker, ms in series:
            ax.plot(
                xs,
                [r[key] for r in rows],
                linestyle=ls,
                linewidth=1.4,
                color=colour,
                marker=marker,
                markersize=ms,
                markerfacecolor=colour,
                markeredgecolor=edge,
                markeredgewidth=0.6,
                label=label,
                clip_on=False,
                zorder=3,
            )

        ax.set_title(r"$d = %d$" % d, pad=5)
        ax.set_xlim(-0.5, len(rows) - 0.5)
        ax.grid(axis="x", visible=False)  # categorical axis: no vertical rules

        # A little headroom so the top markers and the legend do not touch.
        lo = min(r["station_r"] for r in rows)
        hi = max(max(r["lit_r"], r["ae_r"]) for r in rows)
        span = hi - lo
        ax.set_ylim(lo - 0.10 * span, hi + 0.30 * span)

        ax.set_xticks(xs)
        # Equal panel widths mean the d=3 panel packs 14 slots into the space
        # the d=5 panel gives 4, so its labels shrink to stay legible.
        ax.set_xticklabels(
            [str(p) for p in ps], fontsize=6.8 if len(rows) > 8 else 7.6
        )

    axes[0].set_ylabel(r"$|K_{p}|\,/\,B_{p,d}$ (lower is better)")
    axes[1].set_xlabel(r"prime $p$")
    # Single shared legend below the panels: inside any panel it would sit on
    # top of the curves, which all run close to the top of their axes.
    handles, labels = axes[0].get_legend_handles_labels()
    # With the frame off there is no box edge between the legend row and the
    # "prime p" labels above it, so top padding inside the legend has to open
    # that gap. borderpad is set to 0 globally, so it is raised here alone.
    fig.legend(
        handles,
        labels,
        loc="lower center",
        bbox_to_anchor=(0.5, -0.08),
        ncol=3,
        columnspacing=1.6,
        borderpad=0.0,
    )
    save(fig, "kakeya_ratio")


def main():
    records, by_d = load_data()
    assert len(records) == 25, "expected 25 cells, got %d" % len(records)
    assert [len(by_d[d]) for d in DIMS] == [14, 7, 4]

    # The claim the figure has to support, re-derived from the data on every run
    # so the caption can never drift from figdata.json.
    verdicts = [cell_verdict(r)[2] for r in records]
    n_win = sum(1 for s in verdicts if s > 0)
    n_tie = sum(1 for s in verdicts if s == 0)
    n_loss = sum(1 for s in verdicts if s < 0)
    assert (n_win, n_tie, n_loss) == (14, 11, 0), (n_win, n_tie, n_loss)
    print("tally: %d strictly better, %d exact ties, %d worse" % (n_win, n_tie, n_loss))

    fig_ratio(by_d)


if __name__ == "__main__":
    main()
