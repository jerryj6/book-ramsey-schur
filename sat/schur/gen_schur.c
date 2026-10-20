#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static int n;
static int k[3];
static int reach_base[3];
static uint64_t emitted_clauses;

static int parse_positive(const char *text, const char *name)
{
    char *end;
    errno = 0;
    long value = strtol(text, &end, 10);
    if (errno || *text == '\0' || *end != '\0' || value <= 0 || value > INT_MAX) {
        fprintf(stderr, "%s must be a positive integer\n", name);
        exit(EXIT_FAILURE);
    }
    return (int)value;
}

static int color_var(int x, int color)
{
    return 3 * (x - 1) + color + 1;
}

static int reach_var(int color, int count, int sum)
{
    return reach_base[color] + (count - 1) * n + sum - 1;
}

static void emit_clause2(int a, int b)
{
    printf("%d %d 0\n", a, b);
    emitted_clauses++;
}

static void emit_clause3(int a, int b, int c)
{
    printf("%d %d %d 0\n", a, b, c);
    emitted_clauses++;
}

static void print_dimacs(uint64_t variables, uint64_t clauses)
{
    printf("c gen_schur forward-only reachability encoding\n");
    printf("c Color variables: x(i,color)=3*(i-1)+color, i=1..N, color=1..3.\n");
    printf("c Reachability variables follow, ordered by color, count, then sum.\n");
    printf("c R(color,j,x) means x is a sum of exactly j positive integers of that color.\n");
    printf("c No direct solution clauses are emitted.\n");
    printf("p cnf %" PRIu64 " %" PRIu64 "\n", variables, clauses);

    for (int x = 1; x <= n; x++) {
        emit_clause3(color_var(x, 0), color_var(x, 1), color_var(x, 2));
        emit_clause2(-color_var(x, 0), -color_var(x, 1));
        emit_clause2(-color_var(x, 0), -color_var(x, 2));
        emit_clause2(-color_var(x, 1), -color_var(x, 2));
    }

    for (int color = 0; color < 3; color++) {
        for (int x = 1; x <= n; x++)
            emit_clause2(-color_var(x, color), reach_var(color, 1, x));

        for (int count = 2; count < k[color]; count++) {
            for (int y = 1; y <= n; y++) {
                for (int a = 1; a <= n - y; a++) {
                    emit_clause3(-reach_var(color, count - 1, y),
                                 -color_var(a, color),
                                 reach_var(color, count, y + a));
                }
            }
        }

        for (int x = 1; x <= n; x++)
            emit_clause2(-reach_var(color, k[color] - 1, x),
                         -color_var(x, color));
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

int main(int argc, char **argv)
{
    if (argc != 5) {
        fprintf(stderr, "usage: %s N k1 k2 k3\n", argv[0]);
        return EXIT_FAILURE;
    }

    n = parse_positive(argv[1], "N");
    for (int color = 0; color < 3; color++)
        k[color] = parse_positive(argv[color + 2], "k");
    for (int color = 0; color < 3; color++) {
        if (k[color] < 2) {
            fprintf(stderr, "k values must be at least 2\n");
            return EXIT_FAILURE;
        }
    }

    if ((uint64_t)n * 3 > INT_MAX) {
        fprintf(stderr, "N is too large for DIMACS variable identifiers\n");
        return EXIT_FAILURE;
    }

    uint64_t variables = (uint64_t)n * 3;
    for (int color = 0; color < 3; color++) {
        uint64_t reach_count = (uint64_t)(k[color] - 1) * (uint64_t)n;
        if (reach_count > (uint64_t)INT_MAX ||
            variables > (uint64_t)INT_MAX - reach_count) {
            fprintf(stderr, "instance is too large for DIMACS variable identifiers\n");
            return EXIT_FAILURE;
        }
        reach_base[color] = (int)variables + 1;
        variables += reach_count;
    }

    uint64_t clauses = (uint64_t)n * 10;
    uint64_t pairs = (uint64_t)n * (uint64_t)(n - 1) / 2;
    uint64_t recurrence_levels = 0;
    for (int color = 0; color < 3; color++)
        recurrence_levels += (uint64_t)(k[color] - 2);
    if (recurrence_levels && pairs > (UINT64_MAX - clauses) / recurrence_levels) {
        fprintf(stderr, "instance clause count overflows 64-bit arithmetic\n");
        return EXIT_FAILURE;
    }
    clauses += pairs * recurrence_levels;

    print_dimacs(variables, clauses);
    return EXIT_SUCCESS;
}
