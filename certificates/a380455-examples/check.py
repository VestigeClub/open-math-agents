"""Reproduce the 14- and 16-cell prime-polyomino factor bounds using Python 3.

Run with Python 3. Use --json to print all maximizing boards and both histograms.
The catalogue includes reflections.
"""
from collections import Counter
from functools import lru_cache
from itertools import product
import argparse
import json
DIRECTIONS = ((1, 0), (-1, 0), (0, 1), (0, -1))
MOTIONS = tuple(product((False, True), repeat=3))


def turn(shape, motion):
    swap, flip_x, flip_y = motion
    sx, sy = (-1 if flip_x else 1), (-1 if flip_y else 1)
    return tuple((sx * (y if swap else x), sy * (x if swap else y))
                 for x, y in shape)


def normalize(shape):
    x0 = min(x for x, _ in shape)
    y0 = min(y for _, y in shape)
    return tuple(sorted((x - x0, y - y0) for x, y in shape))


@lru_cache(maxsize=None)
def orientations(shape):
    return tuple(sorted({normalize(turn(shape, motion)) for motion in MOTIONS}))


def canonical(shape):
    return min(normalize(turn(shape, motion)) for motion in MOTIONS)


def connected(shape):
    pending = set(shape)
    reached = {pending.pop()}
    frontier = list(reached)
    while frontier:
        x, y = frontier.pop()
        for dx, dy in DIRECTIONS:
            p = (x + dx, y + dy)
            if p in pending:
                pending.remove(p)
                reached.add(p)
                frontier.append(p)
    return not pending


def catalogue():
    levels = {1: (((0, 0),),)}
    for size in range(2, 9):
        found = set()
        for shape in levels[size - 1]:
            occupied = set(shape)
            for x, y in shape:
                for dx, dy in DIRECTIONS:
                    p = (x + dx, y + dy)
                    if p not in occupied:
                        found.add(canonical(occupied | {p}))
        levels[size] = tuple(sorted(found))
    assert [len(levels[n]) for n in range(1, 9)] == [1, 1, 2, 5, 12, 35, 108, 369]
    for size, shapes in levels.items():
        assert all(len(s) == size and connected(s) and canonical(s) == s for s in shapes)
    return levels


def tiles(board, factor):
    """Exact cover by all translated orientations of factor, represented by bits."""
    if len(board) % len(factor):
        return False
    index = {p: i for i, p in enumerate(board)}
    placements = set()
    for oriented in orientations(factor):
        x0, y0 = oriented[0]
        for bx, by in board:
            cells = [(bx + x - x0, by + y - y0) for x, y in oriented]
            if all(p in index for p in cells):
                placements.add(sum(1 << index[p] for p in cells))
    by_cell = [[] for _ in board]
    for mask in placements:
        for i in range(len(board)):
            if mask & (1 << i):
                by_cell[i].append(mask)

    @lru_cache(maxsize=None)
    def cover(left):
        if not left:
            return True
        pivot = (left & -left).bit_length() - 1
        return any(mask & left == mask and cover(left ^ mask)
                   for mask in by_cell[pivot])

    return cover((1 << len(board)) - 1)


def prime_catalogue(levels):
    primes = {}
    for size, shapes in levels.items():
        primes[size] = tuple(s for s in shapes if size > 1 and not any(
            tiles(s, t) for d in range(2, size) if size % d == 0 for t in levels[d]))
    assert [len(primes[n]) for n in (2, 4, 7, 8)] == [1, 1, 108, 145]
    assert primes[4][0] == ((0, 0), (0, 1), (0, 2), (1, 1))
    return primes


def doubled_boards(factor):
    """Every connected union of two disjoint congruent copies, modulo motion."""
    occupied = set(factor)
    boundary = {(x + dx, y + dy) for x, y in factor for dx, dy in DIRECTIONS} - occupied
    raw = set()
    for oriented in orientations(factor):
        offsets = {(bx - tx, by - ty) for bx, by in boundary for tx, ty in oriented}
        for dx, dy in offsets:
            second = {(x + dx, y + dy) for x, y in oriented}
            if occupied.isdisjoint(second):
                raw.add(normalize(occupied | second))
    return {canonical(board) for board in raw}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json', action='store_true', help='Print the complete enumeration as JSON.')
    details = parser.parse_args().json
    levels = catalogue()
    primes = prime_catalogue(levels)
    assert tiles(((0, 0), (0, 1), (1, 0), (1, 1)), primes[2][0])
    assert not tiles(primes[4][0], primes[2][0])
    assert all(tiles(shape, shape) for shape in primes[7] + primes[8])
    results = {}
    for area in (14, 16):
        half = area // 2
        incidence = {}
        for factor_id, factor in enumerate(primes[half]):
            boards = doubled_boards(factor)
            for board in boards:
                incidence.setdefault(board, set()).add(factor_id)
        small = tuple(t for size in range(2, half) if area % size == 0 for t in primes[size])
        total_histogram = Counter()
        large_histogram = Counter()
        maximum, maximizers = 0, []
        exceptions = []
        for board, ids in sorted(incidence.items()):
            small_ids = [i for i, factor in enumerate(small) if tiles(board, factor)]
            total = len(ids) + len(small_ids)
            total_histogram[total] += 1
            large_histogram[len(ids)] += 1
            if total > maximum:
                maximum, maximizers = total, []
            if total == maximum:
                maximizers.append(dict(board=board, half_factor_ids=sorted(ids), small_factor_ids=small_ids))
            if area == 16 and len(ids) > 10:
                exceptions.append(dict(board=board, half_factor_count=len(ids), small_factor_count=len(small_ids)))
        expected_boards, expected_max, expected_winners = (7651, 10, 3) if area == 14 else (12829, 12, 1)
        assert len(incidence) == expected_boards and maximum == expected_max
        assert len(maximizers) == expected_winners
        assert max(large_histogram) == (9 if area == 14 else 12)
        if area == 16:
            assert len(exceptions) == 1 and exceptions[0]['half_factor_count'] == 12
            assert exceptions[0]['small_factor_count'] == 0
        # Independently retest every half factor on each maximizer. This catches
        # an incidence insertion or representative bookkeeping error.
        for winner in maximizers:
            actual = [i for i, factor in enumerate(primes[half]) if tiles(winner['board'], factor)]
            assert actual == winner['half_factor_ids']
            assert connected(winner['board']) and len(winner['board']) == area
        results[str(area)] = dict(
            half_prime_count=len(primes[half]), small_prime_count=len(small),
            boards_with_half_factor=len(incidence), maximum=maximum,
            maximizers=maximizers, large_factor_histogram=dict(sorted(large_histogram.items())),
            total_factor_histogram=dict(sorted(total_histogram.items())), exceptional=exceptions)
        if not details:
            print(f"{area} cells: {len(incidence):,} board classes with a prime factor of area {half}, "
                  f"maximum {maximum}, attained by {len(maximizers)} classes")
    if details:
        report = dict(free_shape_counts={str(n): len(v) for n, v in levels.items()},
                      prime_shape_counts={str(n): len(v) for n, v in primes.items()}, results=results)
        print(json.dumps(report, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
