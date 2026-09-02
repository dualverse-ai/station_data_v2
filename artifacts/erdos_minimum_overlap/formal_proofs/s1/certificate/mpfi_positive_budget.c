/*
 * Directed-rounding verifier for a minimum-overlap dual row.
 *
 * It computes an upper bound on integral_{-2}^2 max(G(x),0) dx using MPFI.
 * The entire domain is covered by interval cells.  Cells on which interval
 * evaluation proves G <= 0 contribute zero; cells proving G >= 0 are grouped
 * and integrated through an interval antiderivative; undecided cells are
 * recursively bisected.  At the depth limit, width*max(sup(G),0) is charged,
 * so a missed or tangential root cannot invalidate the upper bound.
 *
 * Build example:
 *   gcc -O3 -I"$CONDA_PREFIX/include" mpfi_positive_budget.c \
 *       "$CONDA_PREFIX/lib/libmpfi.a" -lmpfr -lgmp -lm \
 *       -o mpfi_positive_budget
 */

#include <stdio.h>
#include <errno.h>
#include <math.h>
#include <mpfr.h>
#include <mpfi.h>
#include <stdlib.h>
#include <string.h>

#define PREC 128

typedef struct {
    size_t n;
    mpfi_t a0, a1, a2, second_derivative_bound;
    mpfi_t *xi, *alpha, *beta;
} Row;

typedef struct {
    unsigned long negative_cells;
    unsigned long positive_cells;
    unsigned long split_cells;
    unsigned long terminal_cells;
    unsigned long max_depth_seen;
    int pending_positive;
    mpfr_t pending_lo;
    mpfr_t pending_hi;
    mpfi_t positive_integral;
    mpfi_t uncertain_integral;
} Audit;

static void die(const char *message) {
    fprintf(stderr, "%s\n", message);
    exit(2);
}

static void set_decimal(mpfi_t out, const char *text) {
    if (mpfi_set_str(out, text, 10) != 0) {
        fprintf(stderr, "cannot parse decimal: %s\n", text);
        exit(2);
    }
}

static void row_init(Row *row, size_t n) {
    row->n = n;
    mpfi_init2(row->a0, PREC);
    mpfi_init2(row->a1, PREC);
    mpfi_init2(row->a2, PREC);
    mpfi_init2(row->second_derivative_bound, PREC);
    row->xi = malloc(n * sizeof(mpfi_t));
    row->alpha = malloc(n * sizeof(mpfi_t));
    row->beta = malloc(n * sizeof(mpfi_t));
    if (!row->xi || !row->alpha || !row->beta) die("allocation failure");
    for (size_t i = 0; i < n; ++i) {
        mpfi_init2(row->xi[i], PREC);
        mpfi_init2(row->alpha[i], PREC);
        mpfi_init2(row->beta[i], PREC);
    }
}

static void row_clear(Row *row) {
    for (size_t i = 0; i < row->n; ++i) {
        mpfi_clear(row->xi[i]);
        mpfi_clear(row->alpha[i]);
        mpfi_clear(row->beta[i]);
    }
    free(row->xi);
    free(row->alpha);
    free(row->beta);
    mpfi_clear(row->a0);
    mpfi_clear(row->a1);
    mpfi_clear(row->a2);
    mpfi_clear(row->second_derivative_bound);
}

static void read_row(const char *path, Row *row) {
    FILE *fh = fopen(path, "r");
    if (!fh) {
        fprintf(stderr, "cannot open %s: %s\n", path, strerror(errno));
        exit(2);
    }
    char a0[128], a1[128], a2[128];
    size_t n;
    if (fscanf(fh, "%127s %127s %127s %zu", a0, a1, a2, &n) != 4) {
        die("bad row header");
    }
    row_init(row, n);
    set_decimal(row->a0, a0);
    set_decimal(row->a1, a1);
    set_decimal(row->a2, a2);
    for (size_t i = 0; i < n; ++i) {
        char xi[128], alpha[128], beta[128];
        if (fscanf(fh, "%127s %127s %127s", xi, alpha, beta) != 3) {
            die("bad row atom");
        }
        set_decimal(row->xi[i], xi);
        set_decimal(row->alpha[i], alpha);
        set_decimal(row->beta[i], beta);
    }
    mpfi_t temp, magnitude, xi2;
    mpfi_init2(temp, PREC);
    mpfi_init2(magnitude, PREC);
    mpfi_init2(xi2, PREC);
    mpfi_abs(row->second_derivative_bound, row->a2);
    mpfi_mul_ui(row->second_derivative_bound, row->second_derivative_bound, 2);
    for (size_t i = 0; i < n; ++i) {
        mpfi_abs(magnitude, row->alpha[i]);
        mpfi_abs(temp, row->beta[i]);
        mpfi_add(magnitude, magnitude, temp);
        mpfi_sqr(xi2, row->xi[i]);
        mpfi_mul(temp, magnitude, xi2);
        mpfi_add(row->second_derivative_bound, row->second_derivative_bound, temp);
    }
    mpfi_clear(temp);
    mpfi_clear(magnitude);
    mpfi_clear(xi2);
    fclose(fh);
}

static void eval_g(mpfi_t out, const Row *row, const mpfi_t x) {
    mpfi_t x2, arg, trig, term;
    mpfi_init2(x2, PREC);
    mpfi_init2(arg, PREC);
    mpfi_init2(trig, PREC);
    mpfi_init2(term, PREC);

    mpfi_sqr(x2, x);
    mpfi_mul(out, row->a1, x);
    mpfi_mul(term, row->a2, x2);
    mpfi_add(out, out, term);
    mpfi_add(out, out, row->a0);
    for (size_t i = 0; i < row->n; ++i) {
        mpfi_mul(arg, row->xi[i], x);
        mpfi_cos(trig, arg);
        mpfi_mul(term, row->alpha[i], trig);
        mpfi_sub(out, out, term);
        mpfi_sin(trig, arg);
        mpfi_mul(term, row->beta[i], trig);
        mpfi_sub(out, out, term);
    }
    mpfi_clear(x2);
    mpfi_clear(arg);
    mpfi_clear(trig);
    mpfi_clear(term);
}

/* Taylor enclosure on [lo,hi], using simultaneous point enclosures for G and
 * G' at the midpoint and a global rigorous bound on |G''|. */
static void eval_g_taylor_range(mpfi_t out, const Row *row, const mpfr_t lo, const mpfr_t hi) {
    mpfr_t mid_fr, radius_fr, left_radius_fr, right_radius_fr, neg_radius_fr;
    mpfr_init2(mid_fr, PREC);
    mpfr_init2(radius_fr, PREC);
    mpfr_init2(left_radius_fr, PREC);
    mpfr_init2(right_radius_fr, PREC);
    mpfr_init2(neg_radius_fr, PREC);
    mpfr_add(mid_fr, lo, hi, MPFR_RNDN);
    mpfr_div_ui(mid_fr, mid_fr, 2, MPFR_RNDN);
    /* Use the larger directed distance from the rounded midpoint.  This
     * explicitly guarantees [lo,hi] is contained in mid+[-radius,radius],
     * even when the exact midpoint is not representable at PREC bits. */
    mpfr_sub(left_radius_fr, mid_fr, lo, MPFR_RNDU);
    mpfr_sub(right_radius_fr, hi, mid_fr, MPFR_RNDU);
    mpfr_max(radius_fr, left_radius_fr, right_radius_fr, MPFR_RNDU);
    mpfr_neg(neg_radius_fr, radius_fr, MPFR_RNDD);

    mpfi_t x, g, gp, arg, sn, cs, term, temp, delta, remainder, radius;
    mpfi_init2(x, PREC);
    mpfi_init2(g, PREC);
    mpfi_init2(gp, PREC);
    mpfi_init2(arg, PREC);
    mpfi_init2(sn, PREC);
    mpfi_init2(cs, PREC);
    mpfi_init2(term, PREC);
    mpfi_init2(temp, PREC);
    mpfi_init2(delta, PREC);
    mpfi_init2(remainder, PREC);
    mpfi_init2(radius, PREC);
    mpfi_set_fr(x, mid_fr);
    mpfi_set_fr(radius, radius_fr);
    mpfi_interv_fr(delta, neg_radius_fr, radius_fr);

    mpfi_sqr(temp, x);
    mpfi_mul(g, row->a1, x);
    mpfi_mul(term, row->a2, temp);
    mpfi_add(g, g, term);
    mpfi_add(g, g, row->a0);
    mpfi_mul_ui(gp, row->a2, 2);
    mpfi_mul(gp, gp, x);
    mpfi_add(gp, gp, row->a1);
    for (size_t i = 0; i < row->n; ++i) {
        mpfi_mul(arg, row->xi[i], x);
        mpfi_sin(sn, arg);
        mpfi_cos(cs, arg);
        mpfi_mul(term, row->alpha[i], cs);
        mpfi_sub(g, g, term);
        mpfi_mul(term, row->beta[i], sn);
        mpfi_sub(g, g, term);
        mpfi_mul(term, row->alpha[i], row->xi[i]);
        mpfi_mul(term, term, sn);
        mpfi_add(gp, gp, term);
        mpfi_mul(term, row->beta[i], row->xi[i]);
        mpfi_mul(term, term, cs);
        mpfi_sub(gp, gp, term);
    }
    mpfi_mul(temp, gp, delta);
    mpfi_add(out, g, temp);
    mpfi_sqr(remainder, radius);
    mpfi_mul(remainder, remainder, row->second_derivative_bound);
    mpfi_div_ui(remainder, remainder, 2);
    mpfr_t rem_lo, rem_hi;
    mpfr_init2(rem_lo, PREC);
    mpfr_init2(rem_hi, PREC);
    mpfi_get_right(rem_hi, remainder);
    mpfr_neg(rem_lo, rem_hi, MPFR_RNDD);
    mpfi_interv_fr(temp, rem_lo, rem_hi);
    mpfi_add(out, out, temp);

    mpfr_clear(rem_lo);
    mpfr_clear(rem_hi);
    mpfi_clear(x);
    mpfi_clear(g);
    mpfi_clear(gp);
    mpfi_clear(arg);
    mpfi_clear(sn);
    mpfi_clear(cs);
    mpfi_clear(term);
    mpfi_clear(temp);
    mpfi_clear(delta);
    mpfi_clear(remainder);
    mpfi_clear(radius);
    mpfr_clear(mid_fr);
    mpfr_clear(radius_fr);
    mpfr_clear(left_radius_fr);
    mpfr_clear(right_radius_fr);
    mpfr_clear(neg_radius_fr);
}

static void eval_antiderivative(mpfi_t out, const Row *row, const mpfi_t x) {
    mpfi_t x2, x3, arg, trig, term, denom;
    mpfi_init2(x2, PREC);
    mpfi_init2(x3, PREC);
    mpfi_init2(arg, PREC);
    mpfi_init2(trig, PREC);
    mpfi_init2(term, PREC);
    mpfi_init2(denom, PREC);

    mpfi_sqr(x2, x);
    mpfi_mul(x3, x2, x);
    mpfi_mul(out, row->a0, x);
    mpfi_mul(term, row->a1, x2);
    mpfi_div_ui(term, term, 2);
    mpfi_add(out, out, term);
    mpfi_mul(term, row->a2, x3);
    mpfi_div_ui(term, term, 3);
    mpfi_add(out, out, term);

    for (size_t i = 0; i < row->n; ++i) {
        mpfi_set(denom, row->xi[i]);
        mpfi_mul(arg, row->xi[i], x);
        mpfi_sin(trig, arg);
        mpfi_mul(term, row->alpha[i], trig);
        mpfi_div(term, term, denom);
        mpfi_sub(out, out, term);
        mpfi_cos(trig, arg);
        mpfi_mul(term, row->beta[i], trig);
        mpfi_div(term, term, denom);
        mpfi_add(out, out, term);
    }
    mpfi_clear(x2);
    mpfi_clear(x3);
    mpfi_clear(arg);
    mpfi_clear(trig);
    mpfi_clear(term);
    mpfi_clear(denom);
}

static int interval_nonpositive(const mpfi_t x) {
    mpfr_t hi;
    mpfr_init2(hi, PREC);
    mpfi_get_right(hi, x);
    int result = mpfr_sgn(hi) <= 0;
    mpfr_clear(hi);
    return result;
}

static int interval_nonnegative(const mpfi_t x) {
    mpfr_t lo;
    mpfr_init2(lo, PREC);
    mpfi_get_left(lo, x);
    int result = mpfr_sgn(lo) >= 0;
    mpfr_clear(lo);
    return result;
}

static void add_exact_integral(Audit *audit, const Row *row, const mpfr_t lo, const mpfr_t hi) {
    mpfi_t xlo, xhi, flo, fhi, contribution;
    mpfi_init2(xlo, PREC);
    mpfi_init2(xhi, PREC);
    mpfi_init2(flo, PREC);
    mpfi_init2(fhi, PREC);
    mpfi_init2(contribution, PREC);
    mpfi_set_fr(xlo, lo);
    mpfi_set_fr(xhi, hi);
    eval_antiderivative(flo, row, xlo);
    eval_antiderivative(fhi, row, xhi);
    mpfi_sub(contribution, fhi, flo);
    mpfi_add(audit->positive_integral, audit->positive_integral, contribution);
    mpfi_clear(xlo);
    mpfi_clear(xhi);
    mpfi_clear(flo);
    mpfi_clear(fhi);
    mpfi_clear(contribution);
}

static void extend_positive_run(Audit *audit, const mpfr_t lo, const mpfr_t hi) {
    if (!audit->pending_positive) {
        mpfr_set(audit->pending_lo, lo, MPFR_RNDD);
        audit->pending_positive = 1;
    }
    mpfr_set(audit->pending_hi, hi, MPFR_RNDU);
}

static void flush_positive_run(Audit *audit, const Row *row) {
    if (!audit->pending_positive) return;
    add_exact_integral(audit, row, audit->pending_lo, audit->pending_hi);
    audit->pending_positive = 0;
}

static void add_uncertain_rectangle(Audit *audit, const mpfi_t gx, const mpfr_t lo, const mpfr_t hi) {
    mpfr_t upper, width;
    mpfi_t charge;
    mpfr_init2(upper, PREC);
    mpfr_init2(width, PREC);
    mpfi_init2(charge, PREC);
    mpfi_get_right(upper, gx);
    if (mpfr_sgn(upper) > 0) {
        mpfr_sub(width, hi, lo, MPFR_RNDU);
        mpfi_set_fr(charge, upper);
        mpfi_mul_fr(charge, charge, width);
        mpfi_add(audit->uncertain_integral, audit->uncertain_integral, charge);
    }
    mpfr_clear(upper);
    mpfr_clear(width);
    mpfi_clear(charge);
}

static void verify_cell(
    Audit *audit,
    const Row *row,
    const mpfr_t lo,
    const mpfr_t hi,
    unsigned depth,
    unsigned max_depth
) {
    mpfi_t x, gx;
    mpfi_init2(x, PREC);
    mpfi_init2(gx, PREC);
    mpfi_interv_fr(x, lo, hi);
    eval_g_taylor_range(gx, row, lo, hi);
    if (interval_nonpositive(gx)) {
        flush_positive_run(audit, row);
        audit->negative_cells++;
    } else if (interval_nonnegative(gx)) {
        audit->positive_cells++;
        extend_positive_run(audit, lo, hi);
    } else if (depth >= max_depth) {
        flush_positive_run(audit, row);
        audit->terminal_cells++;
        add_uncertain_rectangle(audit, gx, lo, hi);
    } else {
        mpfr_t mid;
        mpfr_init2(mid, PREC);
        mpfr_add(mid, lo, hi, MPFR_RNDN);
        mpfr_div_ui(mid, mid, 2, MPFR_RNDN);
        audit->split_cells++;
        if (depth + 1 > audit->max_depth_seen) audit->max_depth_seen = depth + 1;
        verify_cell(audit, row, lo, mid, depth + 1, max_depth);
        verify_cell(audit, row, mid, hi, depth + 1, max_depth);
        mpfr_clear(mid);
    }
    mpfi_clear(x);
    mpfi_clear(gx);
}

static void print_upper(const char *label, const mpfi_t value) {
    mpfr_t upper;
    mpfr_init2(upper, PREC);
    mpfi_get_right(upper, value);
    printf("%s=", label);
    mpfr_out_str(stdout, 10, 30, upper, MPFR_RNDU);
    putchar('\n');
    mpfr_clear(upper);
}

static void print_lower(const char *label, const mpfi_t value) {
    mpfr_t lower;
    mpfr_init2(lower, PREC);
    mpfi_get_left(lower, value);
    printf("%s=", label);
    mpfr_out_str(stdout, 10, 30, lower, MPFR_RNDD);
    putchar('\n');
    mpfr_clear(lower);
}

/* Rigorous upper bound for the support charge
 *   sum sinc(xi)^2 (alpha + beta^2/alpha).
 * Point decimal inputs are converted to intervals by MPFI. */
static void compute_support_charge(mpfi_t support, const Row *row) {
    mpfi_t sn, sinc, gamma, term, temp;
    mpfi_init2(sn, PREC);
    mpfi_init2(sinc, PREC);
    mpfi_init2(gamma, PREC);
    mpfi_init2(term, PREC);
    mpfi_init2(temp, PREC);
    mpfi_set_ui(support, 0);
    mpfr_t alo, ahi, blo, bhi;
    mpfr_init2(alo, PREC);
    mpfr_init2(ahi, PREC);
    mpfr_init2(blo, PREC);
    mpfr_init2(bhi, PREC);
    for (size_t i = 0; i < row->n; ++i) {
        mpfi_get_left(alo, row->alpha[i]);
        mpfi_get_right(ahi, row->alpha[i]);
        mpfi_get_left(blo, row->beta[i]);
        mpfi_get_right(bhi, row->beta[i]);
        if (mpfr_zero_p(alo) && mpfr_zero_p(ahi)) {
            if (!mpfr_zero_p(blo) || !mpfr_zero_p(bhi)) {
                die("nonzero beta paired with zero alpha");
            }
            continue;
        }
        if (mpfr_sgn(alo) <= 0) die("support alpha is not rigorously positive");
        mpfi_sin(sn, row->xi[i]);
        mpfi_div(sinc, sn, row->xi[i]);
        mpfi_sqr(sinc, sinc);
        mpfi_sqr(temp, row->beta[i]);
        mpfi_div(temp, temp, row->alpha[i]);
        mpfi_add(gamma, row->alpha[i], temp);
        mpfi_mul(term, sinc, gamma);
        mpfi_add(support, support, term);
    }
    mpfr_clear(alo);
    mpfr_clear(ahi);
    mpfr_clear(blo);
    mpfr_clear(bhi);
    mpfi_clear(sn);
    mpfi_clear(sinc);
    mpfi_clear(gamma);
    mpfi_clear(term);
    mpfi_clear(temp);
}

int main(int argc, char **argv) {
    if (argc < 2 || argc > 4) {
        fprintf(stderr, "usage: %s row.tsv [initial_cells=10000] [max_depth=20]\n", argv[0]);
        return 2;
    }
    unsigned long initial_cells = argc >= 3 ? strtoul(argv[2], NULL, 10) : 10000UL;
    unsigned max_depth = argc >= 4 ? (unsigned)strtoul(argv[3], NULL, 10) : 20U;
    if (!initial_cells) die("initial_cells must be positive");

    Row row;
    read_row(argv[1], &row);
    Audit audit = {0};
    mpfr_init2(audit.pending_lo, PREC);
    mpfr_init2(audit.pending_hi, PREC);
    mpfi_init2(audit.positive_integral, PREC);
    mpfi_init2(audit.uncertain_integral, PREC);
    mpfi_set_ui(audit.positive_integral, 0);
    mpfi_set_ui(audit.uncertain_integral, 0);

    mpfr_t lo, hi;
    mpfr_init2(lo, PREC);
    mpfr_init2(hi, PREC);
    for (unsigned long i = 0; i < initial_cells; ++i) {
        long numerator_lo = (long)(4UL * i) - (long)(2UL * initial_cells);
        long numerator_hi = (long)(4UL * (i + 1UL)) - (long)(2UL * initial_cells);
        mpfr_set_si(lo, numerator_lo, MPFR_RNDN);
        mpfr_div_ui(lo, lo, initial_cells, MPFR_RNDN);
        mpfr_set_si(hi, numerator_hi, MPFR_RNDN);
        mpfr_div_ui(hi, hi, initial_cells, MPFR_RNDN);
        verify_cell(&audit, &row, lo, hi, 0, max_depth);
    }
    flush_positive_run(&audit, &row);

    mpfi_t total;
    mpfi_init2(total, PREC);
    mpfi_add(total, audit.positive_integral, audit.uncertain_integral);
    printf("atoms=%zu initial_cells=%lu max_depth=%u\n", row.n, initial_cells, max_depth);
    printf(
        "negative_cells=%lu positive_cells=%lu split_cells=%lu terminal_cells=%lu max_depth_seen=%lu\n",
        audit.negative_cells,
        audit.positive_cells,
        audit.split_cells,
        audit.terminal_cells,
        audit.max_depth_seen
    );
    print_upper("positive_antiderivative_upper", audit.positive_integral);
    print_upper("uncertain_rectangle_upper", audit.uncertain_integral);
    print_upper("total_positive_part_upper", total);

    mpfi_t support, quadratic_c0, temp, guard;
    mpfi_init2(support, PREC);
    mpfi_init2(quadratic_c0, PREC);
    mpfi_init2(temp, PREC);
    mpfi_init2(guard, PREC);
    compute_support_charge(support, &row);
    mpfi_mul_ui(temp, row.a2, 2);
    mpfi_div_ui(temp, temp, 3);
    mpfi_add(quadratic_c0, row.a0, temp);
    mpfi_sub(quadratic_c0, quadratic_c0, support);
    set_decimal(guard, "2e-12");
    mpfi_sub(quadratic_c0, quadratic_c0, guard);
    print_upper("support_charge_upper", support);
    print_lower("quadratic_c0_lower", quadratic_c0);
    print_lower("quadratic_a1_lower", row.a1);
    print_lower("quadratic_a2_lower", row.a2);
    mpfr_t total_hi;
    mpfr_init2(total_hi, PREC);
    mpfi_get_right(total_hi, total);
    printf("budget_pass=%s\n", mpfr_cmp_ui(total_hi, 1) <= 0 ? "true" : "false");

    mpfr_clear(total_hi);
    mpfi_clear(support);
    mpfi_clear(quadratic_c0);
    mpfi_clear(temp);
    mpfi_clear(guard);
    mpfi_clear(total);
    mpfr_clear(lo);
    mpfr_clear(hi);
    mpfi_clear(audit.positive_integral);
    mpfi_clear(audit.uncertain_integral);
    mpfr_clear(audit.pending_lo);
    mpfr_clear(audit.pending_hi);
    row_clear(&row);
    return 0;
}
