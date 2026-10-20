import argparse
import shutil
from pathlib import Path


RESERVE_BYTES = 6 * 1024**3


def instance(s, t, bound, depth, mode):
    if s < 2 or t < 2 or bound < 1 or depth < 0:
        raise ValueError("s and t must be >=2, B >=1, and J >=0")
    if mode not in ("default", "control"):
        raise ValueError("mode must be 'default' or 'control'")

    maximum = s * t - t - 1
    threshold = max(bound + 1, depth + 1, s, t, 4)
    expressions = []
    for a in range(maximum + 1):
        for b in range(-bound, bound + 1):
            if a == 0 and b < 1:
                continue
            if a == maximum and b > (-2 if mode == "control" else -1):
                continue
            if not (1 <= a * threshold + b <= maximum * threshold - 1):
                continue
            expressions.append((a, b))

    for a in range(maximum + 1):
        candidates = [b for ea, b in expressions if ea == a]
        assert all(
            1 <= a * threshold + b <= maximum * threshold - 1
            for b in candidates
        )
        assert all(maximum - a >= 0 for _ in candidates)

    expression_set = set(expressions)
    color = {}
    reach = {}
    padding = {}
    next_variable = 1

    for expression in expressions:
        for i in (1, 2, 3):
            color[(expression, i)] = next_variable
            next_variable += 1

    for i, k in ((1, s), (2, t)):
        for j in range(1, k):
            for expression in expressions:
                reach[(i, j, expression)] = next_variable
                next_variable += 1

    constants = [
        c
        for c in range(1, maximum + 1)
        if (0, c) in expression_set and (c, -c) in expression_set
    ]
    for c in constants:
        for j in range(depth + 1):
            for expression in expressions:
                padding[(c, j, expression)] = next_variable
                next_variable += 1

    def clauses():
        for expression in expressions:
            yield [color[(expression, i)] for i in (1, 2, 3)]
            for i in (1, 2, 3):
                for other in range(i + 1, 4):
                    yield [-color[(expression, i)], -color[(expression, other)]]

        for i, k in ((1, s), (2, t)):
            for expression in expressions:
                yield [
                    -color[(expression, i)],
                    reach[(i, 1, expression)],
                ]
            for j in range(2, k):
                for left in expressions:
                    previous = reach[(i, j - 1, left)]
                    for right in expressions:
                        total = (left[0] + right[0], left[1] + right[1])
                        if total in expression_set:
                            yield [
                                -previous,
                                -color[(right, i)],
                                reach[(i, j, total)],
                            ]
            for expression in expressions:
                yield [
                    -reach[(i, k - 1, expression)],
                    -color[(expression, i)],
                ]

        for c in constants:
            yield [
                -color[((0, c), 3)],
                padding[(c, 0, (c, -c))],
            ]
            for j in range(1, depth + 1):
                for state in expressions:
                    previous = padding[(c, j - 1, state)]
                    for replacement in expressions:
                        total = (
                            state[0] + replacement[0],
                            state[1] - c + replacement[1],
                        )
                        if total in expression_set:
                            yield [
                                -previous,
                                -color[(replacement, 3)],
                                padding[(c, j, total)],
                            ]
            for j in range(depth + 1):
                for expression in expressions:
                    yield [
                        -padding[(c, j, expression)],
                        -color[(expression, 3)],
                    ]

    variable_count = next_variable - 1
    clause_count = 0
    dimacs_bytes = len(f"p cnf {variable_count} 0\n")
    for clause in clauses():
        clause_count += 1
        dimacs_bytes += len(" ".join(map(str, clause))) + 3
    dimacs_bytes += len(
        f"p cnf {variable_count} {clause_count}\n"
    ) - len(f"p cnf {variable_count} 0\n")

    return {
        "maximum": maximum,
        "threshold": threshold,
        "expressions": expressions,
        "variables": variable_count,
        "clauses": clause_count,
        "dimacs_bytes": dimacs_bytes,
        "clauses_iter": clauses,
    }


def main():
    parser = argparse.ArgumentParser(
        description="Independent Python encoding of SYMBOLIC_DESIGN.md"
    )
    parser.add_argument("s", type=int)
    parser.add_argument("t", type=int)
    parser.add_argument("B", type=int)
    parser.add_argument("J", type=int)
    parser.add_argument("mode", nargs="?", choices=("default", "control"), default="default")
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()

    output = args.output.resolve()
    if not output.parent.is_dir():
        raise SystemExit(f"output directory does not exist: {output.parent}")

    built = instance(args.s, args.t, args.B, args.J, args.mode)
    free = shutil.disk_usage(output.parent).free
    if free - built["dimacs_bytes"] < RESERVE_BYTES:
        raise SystemExit(
            "disk reserve preflight failed: "
            f"free={free} projected_output={built['dimacs_bytes']} "
            f"reserve={RESERVE_BYTES}"
        )

    with output.open("w", encoding="ascii", newline="\n") as stream:
        stream.write(
            f"p cnf {built['variables']} {built['clauses']}\n"
        )
        for clause in built["clauses_iter"]():
            stream.write(" ".join(map(str, clause)))
            stream.write(" 0\n")

    actual_bytes = output.stat().st_size
    if actual_bytes != built["dimacs_bytes"]:
        output.unlink()
        raise SystemExit(
            f"DIMACS size mismatch: expected {built['dimacs_bytes']}, "
            f"wrote {actual_bytes}"
        )

    print(
        f"mode={args.mode} M={built['maximum']} u0={built['threshold']} "
        f"expressions={len(built['expressions'])} "
        f"variables={built['variables']} clauses={built['clauses']} "
        f"dimacs_bytes={actual_bytes} output={output}"
    )


if __name__ == "__main__":
    main()
