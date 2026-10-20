#include <ctype.h>
#include <errno.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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

static char *read_file(FILE *input)
{
    size_t length = 0;
    size_t capacity = 4096;
    char *contents = malloc(capacity);
    if (!contents) {
        perror("malloc");
        exit(EXIT_FAILURE);
    }

    for (;;) {
        if (length + 2048 > capacity) {
            if (capacity > SIZE_MAX / 2) {
                fprintf(stderr, "input is too large\n");
                free(contents);
                exit(EXIT_FAILURE);
            }
            capacity *= 2;
            char *next = realloc(contents, capacity);
            if (!next) {
                perror("realloc");
                free(contents);
                exit(EXIT_FAILURE);
            }
            contents = next;
        }
        size_t got = fread(contents + length, 1, capacity - length - 1, input);
        length += got;
        if (got == 0) {
            if (ferror(input)) {
                perror("reading input");
                free(contents);
                exit(EXIT_FAILURE);
            }
            break;
        }
    }
    contents[length] = '\0';
    return contents;
}

static int parse_coloring_string(const char *contents, int n, char *colors)
{
    int count = 0;
    for (const unsigned char *p = (const unsigned char *)contents; *p; p++) {
        if (isspace(*p))
            continue;
        if (*p < '1' || *p > '3' || count >= n)
            return 0;
        colors[count++] = (char)(*p - '1');
    }
    return count == n;
}

static int parse_solver_model(char *contents, int n, char *colors)
{
    if ((size_t)n > (SIZE_MAX - 1) / 3) {
        fprintf(stderr, "model is too large\n");
        return 0;
    }
    size_t primary_variables = (size_t)n * 3;
    signed char *values = calloc(primary_variables + 1, sizeof(*values));
    if (!values) {
        perror("calloc");
        return 0;
    }

    int found_sat = 0;
    int found_model = 0;
    char *line_save = NULL;
    for (char *line = strtok_r(contents, "\n", &line_save);
         line != NULL;
         line = strtok_r(NULL, "\n", &line_save)) {
        while (isspace((unsigned char)*line))
            line++;
        if (*line == 's') {
            if (strstr(line, "SATISFIABLE") && !strstr(line, "UNSATISFIABLE"))
                found_sat = 1;
            continue;
        }
        if (*line != 'v' || !isspace((unsigned char)line[1]))
            continue;

        found_model = 1;
        char *token_save = NULL;
        for (char *token = strtok_r(line + 1, " \t\r", &token_save);
             token != NULL;
             token = strtok_r(NULL, " \t\r", &token_save)) {
            char *end;
            errno = 0;
            long literal = strtol(token, &end, 10);
            if (errno || *token == '\0' || *end != '\0') {
                fprintf(stderr, "malformed literal in solver model: %s\n", token);
                free(values);
                return 0;
            }
            if (literal == 0)
                continue;
            long long variable = literal < 0 ? -(long long)literal : literal;
            if ((uint64_t)variable > primary_variables)
                continue;
            signed char value = literal > 0 ? 1 : -1;
            if (values[variable] && values[variable] != value) {
                fprintf(stderr, "conflicting assignments for variable %lld\n", variable);
                free(values);
                return 0;
            }
            values[variable] = value;
        }
    }

    if (!found_sat || !found_model) {
        fprintf(stderr, "input does not contain a SAT status and model\n");
        free(values);
        return 0;
    }

    for (int x = 1; x <= n; x++) {
        int selected = -1;
        int selected_count = 0;
        for (int color = 0; color < 3; color++) {
            size_t variable = (size_t)3 * (size_t)(x - 1) + (size_t)color + 1;
            if (values[variable] > 0) {
                selected = color;
                selected_count++;
            }
        }
        if (selected_count != 1) {
            fprintf(stderr, "model has %d selected colors for integer %d\n",
                    selected_count, x);
            free(values);
            return 0;
        }
        colors[x - 1] = (char)selected;
    }

    free(values);
    return 1;
}

static int check_coloring(const char *colors, int n, const int k[3])
{
    size_t width = (size_t)n + 1;
    for (int color = 0; color < 3; color++) {
        if ((size_t)k[color] > SIZE_MAX / width) {
            fprintf(stderr, "dynamic-programming table is too large\n");
            return 0;
        }
        size_t cells = (size_t)k[color] * width;
        unsigned char *reachable = calloc(cells, sizeof(*reachable));
        if (!reachable) {
            perror("calloc");
            return 0;
        }
        reachable[0] = 1;

        for (int count = 1; count < k[color]; count++) {
            size_t row = (size_t)count * width;
            size_t previous = (size_t)(count - 1) * width;
            for (int sum = 1; sum <= n; sum++) {
                for (int addend = 1; addend <= sum; addend++) {
                    if (colors[addend - 1] == color &&
                        reachable[previous + (size_t)(sum - addend)]) {
                        reachable[row + (size_t)sum] = 1;
                        break;
                    }
                }
            }
        }

        size_t final_row = (size_t)(k[color] - 1) * width;
        for (int rhs = 1; rhs <= n; rhs++) {
            if (colors[rhs - 1] == color && reachable[final_row + (size_t)rhs]) {
                fprintf(stderr, "FORBIDDEN: color %d has an L(%d) solution with rhs %d\n",
                        color + 1, k[color], rhs);
                free(reachable);
                return 0;
            }
        }
        free(reachable);
    }
    return 1;
}

int main(int argc, char **argv)
{
    if (argc != 6) {
        fprintf(stderr, "usage: %s N k1 k2 k3 coloring-or-kissat-log\n", argv[0]);
        return EXIT_FAILURE;
    }

    int n = parse_positive(argv[1], "N");
    int k[3];
    for (int color = 0; color < 3; color++)
        k[color] = parse_positive(argv[color + 2], "k");
    for (int color = 0; color < 3; color++) {
        if (k[color] < 2) {
            fprintf(stderr, "k values must be at least 2\n");
            return EXIT_FAILURE;
        }
    }
    FILE *input = fopen(argv[5], "r");
    if (!input) {
        perror(argv[5]);
        return EXIT_FAILURE;
    }
    char *contents = read_file(input);
    fclose(input);

    char *first = contents;
    while (isspace((unsigned char)*first))
        first++;

    char *colors = malloc((size_t)n);
    if (!colors) {
        perror("malloc");
        free(contents);
        return EXIT_FAILURE;
    }

    int parsed;
    if (*first >= '1' && *first <= '3')
        parsed = parse_coloring_string(contents, n, colors);
    else
        parsed = parse_solver_model(contents, n, colors);
    if (!parsed) {
        fprintf(stderr, "could not decode a coloring of [1,%d]\n", n);
        free(colors);
        free(contents);
        return EXIT_FAILURE;
    }
    free(contents);

    if (!check_coloring(colors, n, k)) {
        free(colors);
        return EXIT_FAILURE;
    }

    for (int x = 0; x < n; x++)
        putchar(colors[x] + '1');
    putchar('\n');
    if (ferror(stdout)) {
        perror("writing coloring");
        free(colors);
        return EXIT_FAILURE;
    }
    fprintf(stderr, "PASS: no monochromatic L(%d), L(%d), or L(%d) in [1,%d]\n",
            k[0], k[1], k[2], n);
    free(colors);
    return EXIT_SUCCESS;
}
