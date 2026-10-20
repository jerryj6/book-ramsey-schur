#include <assert.h>
#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/statvfs.h>

typedef struct {
    int a;
    int b;
} Expr;

static int s;
static int t;
static int m;
static int bound;
static int replacements;
static int control_mode;
static int u0;
static int top_intercept;
static int constant_count;
static size_t expr_count;
static Expr *exprs;
static uint64_t color_base;
static uint64_t reach_base[2];
static uint64_t padding_base;
static uint64_t variable_count;
static uint64_t emitted_clauses;
static FILE *map_file;

static int parse_positive(const char *text, const char *name)
{
    char *end;
    errno = 0;
    long value = strtol(text, &end, 10);
    if (errno || *text == '\0' || *end != '\0' || value <= 0 ||
        value > INT_MAX - 1) {
        fprintf(stderr, "%s must be a positive integer below INT_MAX\n", name);
        exit(EXIT_FAILURE);
    }
    return (int)value;
}

static int expr_index(int64_t a, int64_t b)
{
    if (a < 0 || a > m)
        return -1;
    if (a == 0) {
        if (b < 1 || b > bound)
            return -1;
        return (int)(b - 1);
    }
    if (a < m) {
        if (b < -bound || b > bound)
            return -1;
        uint64_t width = (uint64_t)bound * 2 + 1;
        uint64_t index = (uint64_t)bound + (uint64_t)(a - 1) * width +
                         (uint64_t)(b + bound);
        return index < expr_count ? (int)index : -1;
    }
    if (b < -bound || b > top_intercept)
        return -1;
    uint64_t width = (uint64_t)bound * 2 + 1;
    uint64_t index = (uint64_t)bound + (uint64_t)(m - 1) * width +
                     (uint64_t)(b + bound);
    return index < expr_count ? (int)index : -1;
}

static void build_expressions(void)
{
    uint64_t width = (uint64_t)bound * 2 + 1;
    uint64_t top_count = (uint64_t)(top_intercept + bound + 1);
    uint64_t count = (uint64_t)bound + (uint64_t)(m - 1) * width + top_count;
    if (count > 5000) {
        fprintf(stderr, "expression set has %" PRIu64
                        " members; refusing an impractical instance\n", count);
        exit(EXIT_FAILURE);
    }
    expr_count = (size_t)count;
    exprs = calloc(expr_count, sizeof(*exprs));
    if (!exprs) {
        perror("allocating expression set");
        exit(EXIT_FAILURE);
    }

    size_t at = 0;
    for (int b = 1; b <= bound; b++)
        exprs[at++] = (Expr){0, b};
    for (int a = 1; a < m; a++)
        for (int b = -bound; b <= bound; b++)
            exprs[at++] = (Expr){a, b};
    for (int b = -bound; b <= top_intercept; b++)
        exprs[at++] = (Expr){m, b};
    if (at != expr_count) {
        fprintf(stderr, "internal expression-count mismatch\n");
        exit(EXIT_FAILURE);
    }

    int64_t upper = (int64_t)m * (int64_t)u0 - 1;
    for (int a = 0; a <= m; a++) {
        int found = 0;
        for (size_t i = 0; i < expr_count; i++) {
            if (exprs[i].a != a)
                continue;
            found = 1;
            int64_t value = (int64_t)exprs[i].a * u0 + exprs[i].b;
            assert(value >= 1);
            assert(value <= upper);
        }
        assert(found);
    }

    for (size_t i = 0; i < expr_count; i++) {
        int expected = expr_index(exprs[i].a, exprs[i].b);
        if (expected != (int)i) {
            fprintf(stderr, "internal expression-index mismatch at %zu\n", i);
            exit(EXIT_FAILURE);
        }
    }
}

static uint64_t color_var(int e, int color)
{
    return color_base + (uint64_t)e * 3 + (uint64_t)color;
}

static uint64_t reach_var(int color, int count, int e)
{
    return reach_base[color] + (uint64_t)(count - 1) * expr_count +
           (uint64_t)e;
}

static uint64_t padding_var(int c, int count, int e)
{
    return padding_base +
           ((uint64_t)(c - 1) * (uint64_t)(replacements + 1) +
            (uint64_t)count) * expr_count + (uint64_t)e;
}

static uint64_t count_reach_transitions(void)
{
    uint64_t count = 0;
    for (size_t first = 0; first < expr_count; first++) {
        for (size_t second = 0; second < expr_count; second++) {
            if (expr_index((int64_t)exprs[first].a + exprs[second].a,
                           (int64_t)exprs[first].b + exprs[second].b) >= 0)
                count++;
        }
    }
    return count;
}

static uint64_t count_padding_transitions(void)
{
    uint64_t count = 0;
    for (int c = 1; c <= constant_count; c++) {
        for (size_t source = 0; source < expr_count; source++) {
            for (size_t addend = 0; addend < expr_count; addend++) {
                int64_t a = (int64_t)exprs[source].a + exprs[addend].a;
                int64_t b = (int64_t)exprs[source].b - c + exprs[addend].b;
                if (expr_index(a, b) >= 0)
                    count++;
            }
        }
    }
    return count;
}

static void write_map_line(uint64_t variable, const char *kind, int i, int c,
                           int j, int a, int b)
{
    if (fprintf(map_file, "%" PRIu64 "\t%s\t%d\t%d\t%d\t%d\t%d\n",
                variable, kind, i, c, j, a, b) < 0) {
        perror("writing gen_sym.map");
        exit(EXIT_FAILURE);
    }
}

static void write_variable_map(void)
{
    map_file = fopen("gen_sym.map", "w");
    if (!map_file) {
        perror("gen_sym.map");
        exit(EXIT_FAILURE);
    }
    fprintf(map_file, "var\tkind\ti\tc\tj\ta\tb\n");

    for (size_t e = 0; e < expr_count; e++)
        for (int color = 1; color <= 3; color++)
            write_map_line(color_var((int)e, color - 1), "COL", color, 0, 0,
                           exprs[e].a, exprs[e].b);

    for (int color = 0; color < 2; color++) {
        int k = color == 0 ? s : t;
        for (int j = 1; j < k; j++)
            for (size_t e = 0; e < expr_count; e++)
                write_map_line(reach_var(color, j, (int)e), "R", color + 1,
                               0, j, exprs[e].a, exprs[e].b);
    }

    for (int c = 1; c <= constant_count; c++)
        for (int j = 0; j <= replacements; j++)
            for (size_t e = 0; e < expr_count; e++)
                write_map_line(padding_var(c, j, (int)e), "P", 3, c, j,
                               exprs[e].a, exprs[e].b);

    if (fclose(map_file) != 0) {
        perror("closing gen_sym.map");
        exit(EXIT_FAILURE);
    }
    map_file = NULL;
}

static void emit_clause2(int64_t a, int64_t b)
{
    printf("%" PRId64 " %" PRId64 " 0\n", a, b);
    emitted_clauses++;
}

static void emit_clause3(int64_t a, int64_t b, int64_t c)
{
    printf("%" PRId64 " %" PRId64 " %" PRId64 " 0\n", a, b, c);
    emitted_clauses++;
}

static void emit_formula(uint64_t clauses)
{
    printf("c gen_sym affine-expression reachability encoding\n");
    printf("c s=%d t=%d M=%d B=%d J=%d u0=%d mode=%s\n",
           s, t, m, bound, replacements, u0,
           control_mode ? "control" : "default");
    printf("c variable map: gen_sym.map\n");
    printf("p cnf %" PRIu64 " %" PRIu64 "\n", variable_count, clauses);

    for (size_t e = 0; e < expr_count; e++) {
        emit_clause3((int64_t)color_var((int)e, 0),
                     (int64_t)color_var((int)e, 1),
                     (int64_t)color_var((int)e, 2));
        emit_clause2(-(int64_t)color_var((int)e, 0),
                     -(int64_t)color_var((int)e, 1));
        emit_clause2(-(int64_t)color_var((int)e, 0),
                     -(int64_t)color_var((int)e, 2));
        emit_clause2(-(int64_t)color_var((int)e, 1),
                     -(int64_t)color_var((int)e, 2));
    }

    for (int color = 0; color < 2; color++) {
        int k = color == 0 ? s : t;
        for (size_t e = 0; e < expr_count; e++)
            emit_clause2(-(int64_t)color_var((int)e, color),
                         (int64_t)reach_var(color, 1, (int)e));
        for (int j = 2; j < k; j++) {
            for (size_t first = 0; first < expr_count; first++) {
                for (size_t second = 0; second < expr_count; second++) {
                    int sum = expr_index(
                        (int64_t)exprs[first].a + exprs[second].a,
                        (int64_t)exprs[first].b + exprs[second].b);
                    if (sum < 0)
                        continue;
                    emit_clause3(-(int64_t)reach_var(color, j - 1, (int)first),
                                 -(int64_t)color_var((int)second, color),
                                 (int64_t)reach_var(color, j, sum));
                }
            }
        }
        for (size_t e = 0; e < expr_count; e++)
            emit_clause2(-(int64_t)reach_var(color, k - 1, (int)e),
                         -(int64_t)color_var((int)e, color));
    }

    for (int c = 1; c <= constant_count; c++) {
        int start = expr_index(0, c);
        int initial = expr_index(c, -c);
        assert(start >= 0 && initial >= 0);
        emit_clause2(-(int64_t)color_var(start, 2),
                     (int64_t)padding_var(c, 0, initial));
        for (int j = 1; j <= replacements; j++) {
            for (size_t source = 0; source < expr_count; source++) {
                for (size_t addend = 0; addend < expr_count; addend++) {
                    int result = expr_index(
                        (int64_t)exprs[source].a + exprs[addend].a,
                        (int64_t)exprs[source].b - c + exprs[addend].b);
                    if (result < 0)
                        continue;
                    emit_clause3(
                        -(int64_t)padding_var(c, j - 1, (int)source),
                        -(int64_t)color_var((int)addend, 2),
                        (int64_t)padding_var(c, j, result));
                }
            }
        }
        for (int j = 0; j <= replacements; j++)
            for (size_t e = 0; e < expr_count; e++)
                emit_clause2(-(int64_t)padding_var(c, j, (int)e),
                             -(int64_t)color_var((int)e, 2));
    }

    if (ferror(stdout)) {
        perror("writing DIMACS");
        exit(EXIT_FAILURE);
    }
    if (emitted_clauses != clauses) {
        fprintf(stderr, "internal clause-count mismatch: expected %" PRIu64
                        ", emitted %" PRIu64 "\n", clauses, emitted_clauses);
        exit(EXIT_FAILURE);
    }
}

static void check_disk_reserve(uint64_t clauses, uint64_t variables)
{
    struct statvfs disk;
    if (statvfs(".", &disk) != 0) {
        perror("checking free disk");
        exit(EXIT_FAILURE);
    }
    long double free_bytes = (long double)disk.f_bavail *
                             (long double)disk.f_frsize;
    long double estimate = (long double)clauses * 32.0L +
                           (long double)variables * 32.0L +
                           (long double)(1U << 20);
    long double reserve = 6.0L * 1024.0L * 1024.0L * 1024.0L;
    if (free_bytes < reserve + estimate) {
        fprintf(stderr, "disk guard: available %.0Lf bytes, estimated output "
                        "%.0Lf bytes plus 6 GiB reserve\n",
                free_bytes, estimate);
        exit(EXIT_FAILURE);
    }
}

int main(int argc, char **argv)
{
    if (argc != 5 && argc != 6) {
        fprintf(stderr, "usage: %s s t B J [control]\n", argv[0]);
        return EXIT_FAILURE;
    }
    s = parse_positive(argv[1], "s");
    t = parse_positive(argv[2], "t");
    bound = parse_positive(argv[3], "B");
    replacements = parse_positive(argv[4], "J");
    if (s < 3 || t < s || bound < 2) {
        fprintf(stderr, "require 3 <= s <= t and B >= 2\n");
        return EXIT_FAILURE;
    }
    if (argc == 6) {
        if (strcmp(argv[5], "control") != 0) {
            fprintf(stderr, "the only supported mode is control\n");
            return EXIT_FAILURE;
        }
        control_mode = 1;
    }

    int64_t computed_m = (int64_t)s * t - t - 1;
    if (computed_m <= 0 || computed_m > INT_MAX) {
        fprintf(stderr, "M=st-t-1 is outside supported range\n");
        return EXIT_FAILURE;
    }
    m = (int)computed_m;
    u0 = bound + 1;
    if (replacements + 1 > u0)
        u0 = replacements + 1;
    if (s > u0)
        u0 = s;
    if (t > u0)
        u0 = t;
    if (u0 < 4)
        u0 = 4;
    top_intercept = control_mode ? -2 : -1;
    constant_count = bound < m ? bound : m;

    build_expressions();
    color_base = 1;
    uint64_t next_variable = (uint64_t)expr_count * 3 + 1;
    for (int color = 0; color < 2; color++) {
        reach_base[color] = next_variable;
        int k = color == 0 ? s : t;
        next_variable += (uint64_t)(k - 1) * expr_count;
    }
    padding_base = next_variable;
    next_variable += (uint64_t)constant_count *
                     (uint64_t)(replacements + 1) * expr_count;
    variable_count = next_variable - 1;
    if (variable_count > INT_MAX) {
        fprintf(stderr, "instance needs %" PRIu64
                        " variables; DIMACS identifiers exceed INT_MAX\n",
                variable_count);
        return EXIT_FAILURE;
    }

    uint64_t reach_transitions = count_reach_transitions();
    uint64_t padding_transitions = count_padding_transitions();
    uint64_t clauses = (uint64_t)expr_count * 8;
    clauses += ((uint64_t)(s - 2) + (uint64_t)(t - 2)) *
               reach_transitions;
    clauses += (uint64_t)constant_count;
    clauses += (uint64_t)replacements * padding_transitions;
    clauses += (uint64_t)constant_count *
               (uint64_t)(replacements + 1) * expr_count;

    check_disk_reserve(clauses, variable_count);
    write_variable_map();
    emit_formula(clauses);
    fprintf(stderr, "vars=%" PRIu64 " clauses=%" PRIu64
                    " expressions=%zu transitions_R=%" PRIu64
                    " transitions_P=%" PRIu64 " u0=%d map=gen_sym.map\n",
            variable_count, clauses, expr_count, reach_transitions,
            padding_transitions, u0);
    free(exprs);
    return EXIT_SUCCESS;
}
