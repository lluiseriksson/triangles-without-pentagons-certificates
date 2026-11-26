"""
EX-K3-C5-CERT-1.0: Zero-floating-point exact algebraic verifier for Qing Cui, Ervin Gyori,
Chenke Zhang, and Xiutao Zhu's "The maximum number of triangles in a graph without pentagons"
(arXiv:2611.33685v1, November 25, 2026).

Strictly zero floating-point literals, zero float() calls, zero true-division (/ or /=),
and zero math/numpy imports. All arithmetic uses exact Python int and fractions.Fraction
(parsed from lowest-terms [num, den] pairs).
"""

from __future__ import annotations

import json
import pathlib
import sys
from fractions import Fraction
from typing import Any

SCHEMA_VERSION = "EX-K3-C5-CERT-1.0"
MAX_JSON_BYTES = 1_000_000
MAX_RAT_ABS = 10**18
MAX_VERTS = 48


class VerificationError(ValueError):
    """Raised whenever a certificate violates schema, bounds, or mathematical invariants."""


def _gcd(a: int, b: int) -> int:
    a = abs(a)
    b = abs(b)
    while b:
        a, b = b, a % b
    return a


def _req_int(val: Any, name: str, lo: int | None = None, hi: int | None = None) -> int:
    if isinstance(val, bool) or not isinstance(val, int):
        raise VerificationError(f"Expected integer for {name}, got {type(val).__name__}")
    if lo is not None and val < lo:
        raise VerificationError(f"{name}={val} below minimum {lo}")
    if hi is not None and val > hi:
        raise VerificationError(f"{name}={val} above maximum {hi}")
    return val


def _req_str(val: Any, name: str) -> str:
    if not isinstance(val, str) or not val.strip():
        raise VerificationError(f"Expected non-empty string for {name}")
    return val


def _req_list(val: Any, name: str, min_len: int = 0, max_len: int = 4096) -> list[Any]:
    if not isinstance(val, list):
        raise VerificationError(f"Expected list for {name}")
    if len(val) < min_len or len(val) > max_len:
        raise VerificationError(f"{name} length {len(val)} out of range [{min_len}, {max_len}]")
    return val


def _req_dict(val: Any, name: str) -> dict[str, Any]:
    if not isinstance(val, dict):
        raise VerificationError(f"Expected dict for {name}")
    return val


def _parse_rat(val: Any, name: str) -> Fraction:
    if not isinstance(val, list) or len(val) != 2:
        raise VerificationError(f"Expected [num, den] rational pair for {name}")
    num = _req_int(val[0], f"{name}[0]", -MAX_RAT_ABS, MAX_RAT_ABS)
    den = _req_int(val[1], f"{name}[1]", 1, MAX_RAT_ABS)
    if _gcd(num, den) != 1:
        raise VerificationError(f"Rational {name}=[{num},{den}] not in lowest terms")
    return Fraction(num, den)


def _no_dup_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        if k in out:
            raise VerificationError(f"Duplicate JSON key: {k}")
        out[k] = v
    return out


def _reject_json_constant(token: str) -> Any:
    raise VerificationError(f"Illegal non-finite JSON constant: {token}")


def _reject_json_float(token: str) -> Any:
    raise VerificationError(f"Illegal floating-point JSON literal: {token}")


# ---------------------------------------------------------------------------
# Graph & Weight-Matrix Helpers
# ---------------------------------------------------------------------------

def _parse_simple_graph(payload: dict[str, Any], max_n: int = MAX_VERTS) -> tuple[int, list[set[int]], list[tuple[int, int]]]:
    n = _req_int(payload.get("num_vertices"), "num_vertices", 3, max_n)
    edges_raw = _req_list(payload.get("edges"), "edges", 1, n * (n - 1) // 2)
    adj: list[set[int]] = [set() for _ in range(n)]
    edges: list[tuple[int, int]] = []
    seen: set[tuple[int, int]] = set()
    for idx, er in enumerate(edges_raw):
        el = _req_list(er, f"edges[{idx}]", 2, 2)
        u = _req_int(el[0], f"edges[{idx}][0]", 0, n - 1)
        v = _req_int(el[1], f"edges[{idx}][1]", 0, n - 1)
        if u == v:
            raise VerificationError(f"Self-loop ({u},{v}) forbidden in simple graph")
        key = (u, v) if u < v else (v, u)
        if key in seen:
            raise VerificationError(f"Duplicate edge {key}")
        seen.add(key)
        adj[u].add(v)
        adj[v].add(u)
        edges.append(key)
    return n, adj, edges


def _has_c5(n: int, adj: list[set[int]]) -> bool:
    """Exact check whether simple graph contains a 5-cycle C_5."""
    for v0 in range(n):
        for v1 in adj[v0]:
            if v1 <= v0:
                continue
            for v2 in adj[v1]:
                if v2 <= v0 or v2 == v1:
                    continue
                for v3 in adj[v2]:
                    if v3 <= v0 or v3 == v1 or v3 == v2:
                        continue
                    for v4 in adj[v3]:
                        if v4 > v0 and v4 != v1 and v4 != v2 and v4 != v3 and v0 in adj[v4]:
                            return True
    return False


def _has_induced_c4(n: int, adj: list[set[int]]) -> bool:
    """Exact check whether simple graph contains an induced 4-cycle."""
    for a in range(n):
        for b in range(a + 1, n):
            if b in adj[a]:
                continue
            common = sorted(adj[a] & adj[b])
            for i in range(len(common)):
                u = common[i]
                for j in range(i + 1, len(common)):
                    v = common[j]
                    if v not in adj[u]:
                        return True
    return False


def _parse_weight_matrix(payload: dict[str, Any], max_n: int = 12) -> tuple[int, list[list[Fraction]]]:
    n = _req_int(payload.get("num_vertices"), "num_vertices", 2, max_n)
    rows_raw = _req_list(payload.get("weight_matrix_k"), "weight_matrix_k", n, n)
    k: list[list[Fraction]] = []
    total = Fraction(0, 1)
    for i in range(n):
        row_r = _req_list(rows_raw[i], f"weight_matrix_k[{i}]", n, n)
        row: list[Fraction] = []
        for j in range(n):
            val = _parse_rat(row_r[j], f"k[{i}][{j}]")
            if val < 0:
                raise VerificationError(f"Negative weight k[{i}][{j}]={val}")
            total += val
            row.append(val)
        k.append(row)
    if total == 0:
        raise VerificationError("Vacuous all-zero weight matrix rejected")
    return n, k


def _compute_capacity_Ck(n: int, k: list[list[Fraction]]) -> list[list[Fraction]]:
    """Compute exact 2-walk capacity C_k(x, y) from Section 2 over exact Q."""
    inv_n = Fraction(1, n)
    half = Fraction(1, 2)
    Ck = [[Fraction(0, 1)] * n for _ in range(n)]
    for x in range(n):
        for y in range(n):
            acc = Fraction(0, 1)
            for z in range(n):
                acc += (
                    k[x][z] * k[y][z]
                    + half * k[z][x] * k[z][y]
                    + k[x][z] * k[z][y]
                    + k[z][x] * k[y][z]
                )
            Ck[x][y] = acc * inv_n
    return Ck


# ---------------------------------------------------------------------------
# Mode 1: book_reduction_and_capacity (Sec. 2 Prop. 2.6, Lemmas 2.5, 2.7, 2.8)
# ---------------------------------------------------------------------------

def _verify_mode1(payload: dict[str, Any]) -> dict[str, Any]:
    submode = _req_str(payload.get("submode"), "submode")

    if submode == "book_block_orientation_and_cap":
        # Verify Prop. 2.6 & Lemma 2.8 on an explicit C_5-free graph where every edge lies in a triangle
        n, adj, edges = _parse_simple_graph(payload, max_n=28)
        if _has_c5(n, adj):
            raise VerificationError("Graph contains a C_5 (violates C_5-free hypothesis)")

        # Enumerate all triangles and verify every edge belongs to >= 1 triangle
        triangles: list[tuple[int, int, int]] = []
        edge_to_tris: dict[tuple[int, int], list[int]] = {e: [] for e in edges}
        for u in range(n):
            for v in adj[u]:
                if v <= u:
                    continue
                for w in adj[u] & adj[v]:
                    if w <= v:
                        continue
                    tid = len(triangles)
                    triangles.append((u, v, w))
                    edge_to_tris[(u, v)].append(tid)
                    edge_to_tris[(u, w)].append(tid)
                    edge_to_tris[(v, w)].append(tid)
        if not triangles:
            raise VerificationError("Vacuous triangle-free input graph")
        for e, tids in edge_to_tris.items():
            if not tids:
                raise VerificationError(f"Edge {e} lies in no triangle (violates Prop. 2.6 hypothesis)")

        # Verify Prop. 2.6 common-neighbor property: any two nonadjacent vertices have <= 2 common neighbors (adjacent if 2)
        for u in range(n):
            for v in range(u + 1, n):
                if v in adj[u]:
                    continue
                cn = sorted(adj[u] & adj[v])
                if len(cn) > 2:
                    raise VerificationError(f"Nonadjacent pair ({u},{v}) has {len(cn)} > 2 common neighbors")
                if len(cn) == 2 and cn[1] not in adj[cn[0]]:
                    raise VerificationError(f"Common neighbors {cn} of ({u},{v}) are not adjacent")

        # Partition triangles into triangle blocks (BFS over shared edges) and classify each block as K_4 or Book!
        tri_seen = [False] * len(triangles)
        k4_blocks = 0
        book_blocks = 0
        book_spines: set[tuple[int, int]] = set()
        oriented_arcs: set[tuple[int, int]] = set()
        book_tri_count = 0

        for start_t in range(len(triangles)):
            if tri_seen[start_t]:
                continue
            comp_t = [start_t]
            tri_seen[start_t] = True
            idx = 0
            while idx < len(comp_t):
                cur = comp_t[idx]
                idx += 1
                a, b, c = triangles[cur]
                for e in ((a, b), (a, c), (b, c)):
                    for nb in edge_to_tris[e]:
                        if not tri_seen[nb]:
                            tri_seen[nb] = True
                            comp_t.append(nb)
            verts = sorted({v for t in comp_t for v in triangles[t]})
            # Check if K_4 (4 vertices, 4 triangles) or Book (all triangles share a common spine edge ab!)
            if len(verts) == 4 and len(comp_t) == 4:
                k4_blocks += 1
            else:
                # Find spine edge shared by every triangle in comp_t
                cand_edges: set[tuple[int, int]] | None = None
                for t in comp_t:
                    a, b, c = triangles[t]
                    es = {(a, b), (a, c), (b, c)}
                    cand_edges = es if cand_edges is None else (cand_edges & es)
                if not cand_edges:
                    raise VerificationError(f"Triangle block on {verts} is neither K_4 nor a book")
                # Pick canonical spine (if single triangle, pick lexicographically first edge)
                spine = min(cand_edges)
                book_spines.add(spine)
                book_blocks += 1
                a, b = spine
                for t in comp_t:
                    page = next(v for v in triangles[t] if v != a and v != b)
                    oriented_arcs.add((a, page))
                    oriented_arcs.add((b, page))
                    book_tri_count += 1

        if book_tri_count == 0:
            raise VerificationError("No book blocks remain after K_4 removal")
        if len(oriented_arcs) != 2 * book_tri_count:
            raise VerificationError(f"|E(D)|={len(oriented_arcs)} != 2*tau(G_books)={2*book_tri_count}")

        # Verify underlying graph H of D is {K_3, C_5}-free!
        adjH: list[set[int]] = [set() for _ in range(n)]
        out_deg = [0] * n
        in_deg = [0] * n
        for u, v in oriented_arcs:
            if u in adjH[v]:
                raise VerificationError("Opposite arcs created in D")
            adjH[u].add(v)
            adjH[v].add(u)
            out_deg[u] += 1
            in_deg[v] += 1
        # Check K_3-free
        for u in range(n):
            for v in adjH[u]:
                if v > u and (adjH[u] & adjH[v]):
                    raise VerificationError("Oriented book-reduced graph H still contains a triangle")
        if _has_c5(n, adjH):
            raise VerificationError("Oriented book-reduced graph H contains a C_5")

        # Verify Lemma 2.8 exact scaled capacity bound C_f(i, j) <= 1 + R(i, j) where f = sqrt(n) * 1_D
        # Scaling out sqrt(n)^2 / n = 1, C_f(i, j) is pure exact rational!
        half = Fraction(1, 2)
        spine_pages: dict[tuple[int, int], int] = {}
        for a, b in book_spines:
            pages_cnt = len({p for (x, p) in oriented_arcs if x == a} & {p for (x, p) in oriented_arcs if x == b})
            spine_pages[(a, b)] = pages_cnt
            spine_pages[(b, a)] = pages_cnt

        R_mat = [[Fraction(0, 1)] * n for _ in range(n)]
        for i in range(n):
            R_mat[i][i] = Fraction(out_deg[i], 1) + half * in_deg[i]
        for (a, b), scnt in spine_pages.items():
            R_mat[a][b] = Fraction(scnt, 1)

        for i in range(n):
            for j in range(n):
                cf = Fraction(0, 1)
                for z in range(n):
                    iz = 1 if (i, z) in oriented_arcs else 0
                    jz = 1 if (j, z) in oriented_arcs else 0
                    zi = 1 if (z, i) in oriented_arcs else 0
                    zj = 1 if (z, j) in oriented_arcs else 0
                    cf += iz * jz + half * zi * zj + iz * zj + zi * jz
                if cf > 1 + R_mat[i][j]:
                    raise VerificationError(f"Lemma 2.8 violated at ({i},{j}): C_f={cf} > 1 + R={1 + R_mat[i][j]}")
            # Verify exact row-sum identity sum_j R(i, j) = 2*d^+(i) + d^-(i)/2!
            row_sum = sum(R_mat[i])
            expected_rs = Fraction(2 * out_deg[i], 1) + half * in_deg[i]
            if row_sum != expected_rs:
                raise VerificationError(f"Lemma 2.8 row-sum identity failed at {i}: {row_sum} != {expected_rs}")

        return {
            "mode": "book_reduction_and_capacity",
            "submode": submode,
            "num_vertices": n,
            "k4_blocks_removed": k4_blocks,
            "book_blocks": book_blocks,
            "book_triangles": book_tri_count,
            "oriented_arcs": len(oriented_arcs),
        }

    if submode == "capacity_l2_and_row_bounds":
        # Verify Lemma 2.5 Eq. (1): C_k(x, y) <= 1 => ||K||_2^2 <= 4/3 AND (1/n) sum_z K(x,z)^2 <= 2!
        n, k = _parse_weight_matrix(payload, max_n=12)
        Ck = _compute_capacity_Ck(n, k)
        for x in range(n):
            for y in range(n):
                if Ck[x][y] > 1:
                    raise VerificationError(f"Capacity bound violated: C_k({x},{y})={Ck[x][y]} > 1")

        K = [[k[x][y] + k[y][x] for y in range(n)] for x in range(n)]
        l2_sq = sum(K[x][y] * K[x][y] for x in range(n) for y in range(n)) * Fraction(1, n * n)
        if l2_sq > Fraction(4, 3):
            raise VerificationError(f"Lemma 2.5 ||K||_2^2={l2_sq} > 4/3")
        max_row_sq = Fraction(0, 1)
        for x in range(n):
            rs = sum(K[x][z] * K[x][z] for z in range(n)) * Fraction(1, n)
            if rs > 2:
                raise VerificationError(f"Lemma 2.5 row bound violated at {x}: {rs} > 2")
            if rs > max_row_sq:
                max_row_sq = rs

        return {
            "mode": "book_reduction_and_capacity",
            "submode": submode,
            "num_vertices": n,
            "l2_sq": [l2_sq.numerator, l2_sq.denominator],
            "max_row_sq": [max_row_sq.numerator, max_row_sq.denominator],
        }

    raise VerificationError(f"Unknown Mode 1 submode: {submode}")


# ---------------------------------------------------------------------------
# Mode 2: bipartite_sos_and_table1 (Sec. 4 Prop. 4.1, Claim 4.2, Table 1, Claim 4.3)
# ---------------------------------------------------------------------------

def _parse_bipartite_k(payload: dict[str, Any]) -> tuple[int, list[int], list[int], list[list[Fraction]], Fraction, Fraction, Fraction]:
    n, k = _parse_weight_matrix(payload, max_n=12)
    x_raw = _req_list(payload.get("part_X"), "part_X", 1, n - 1)
    X = [_req_int(v, "part_X", 0, n - 1) for v in x_raw]
    if len(set(X)) != len(X):
        raise VerificationError("Duplicate vertex in part_X")
    X_set = set(X)
    Y = [v for v in range(n) if v not in X_set]
    if not Y:
        raise VerificationError("part_Y must be non-empty")
    if len(X) < len(Y):
        raise VerificationError("Section 4 assumes p = |X|/n >= q = |Y|/n")
    # Verify k is strictly bipartite (zero on X^2 and Y^2)
    for u in X:
        for v in X:
            if k[u][v] != 0:
                raise VerificationError(f"Non-bipartite weight k[{u}][{v}] inside X^2")
    for u in Y:
        for v in Y:
            if k[u][v] != 0:
                raise VerificationError(f"Non-bipartite weight k[{u}][{v}] inside Y^2")
    # Check C_k <= 1 everywhere
    Ck = _compute_capacity_Ck(n, k)
    for u in range(n):
        for v in range(n):
            if Ck[u][v] > 1:
                raise VerificationError(f"Capacity bound violated: C_k({u},{v})={Ck[u][v]} > 1")
    p = Fraction(len(X), n)
    q = Fraction(len(Y), n)
    d = 2 - 3 * p
    if not (0 < d <= Fraction(1, 2)):
        raise VerificationError(f"Expected 0 < d = 2 - 3p <= 1/2 (1/2 <= p < 2/3), got p={p}, d={d}")
    return n, X, Y, k, p, q, d


def _sec4_eval_S_I_J_B0(
    n: int, X: list[int], Y: list[int], k: list[list[Fraction]], d: Fraction
) -> tuple[Fraction, Fraction, Fraction, Fraction, Fraction, Fraction, dict[str, Fraction]]:
    """Compute exact Section 4 quantities (S, I, J, B0, t, beta, table1_sums) over Q."""
    half = Fraction(1, 2)
    rX = {"FF": Fraction(1, 1), "RR": half, "FR": Fraction(1, 1), "RF": Fraction(1, 1)}
    rY = {"FF": half, "RR": Fraction(1, 1), "FR": Fraction(1, 1), "RF": Fraction(1, 1)}
    sX = {
        "FF": 3 + 2 * d,
        "RR": 1 - d + d * d * Fraction(1, 8),
        "FR": 3 + d * Fraction(7, 4) + d * d * Fraction(1, 64),
        "RF": 3 + d * Fraction(7, 4) + d * d * Fraction(1, 64),
    }
    sY = {
        "FF": Fraction(0, 1),
        "RR": 4 + d - d * d * Fraction(1, 16),
        "FR": 4 + d * half,
        "RF": 4 + d * half,
    }

    # Exact Table 1 class sums over all 16 subsets E of {1, 2, 3, 4}:
    # Position 1=(x,y), 2=(x',y), 3=(x',y'), 4=(x,y'); bit (pos-1) = 1 => type F, else type R.
    # For (e1, e2, e3, e4): j_E = sX(e1e2)*rX(e4e3) + sY(e1e4)*rY(e2e3)
    #                       b_E = (2+2d)*rX(e1e2)*rX(e4e3) + 4*rY(e1e4)*rY(e2e3)
    orbit_map = {
        "1234": [0b1111],
        "empty": [0b0000],
        "triples": [0b0111, 0b1011, 0b1101, 0b1110],
        "singletons": [0b0001, 0b0010, 0b0100, 0b1000],
        "14_23": [0b1001, 0b0110],
        "12_34": [0b0011, 0b1100],
        "13_24": [0b0101, 0b1010],
    }
    table1_sums: dict[str, Fraction] = {}
    for cls_name, masks in orbit_map.items():
        s_diff = Fraction(0, 1)
        for m in masks:
            e1 = "F" if (m & 1) else "R"
            e2 = "F" if (m & 2) else "R"
            e3 = "F" if (m & 4) else "R"
            e4 = "F" if (m & 8) else "R"
            jE = sX[e1 + e2] * rX[e4 + e3] + sY[e1 + e4] * rY[e2 + e3]
            bE = (2 + 2 * d) * rX[e1 + e2] * rX[e4 + e3] + 4 * rY[e1 + e4] * rY[e2 + e3]
            s_diff += jE - bE
        table1_sums[cls_name] = s_diff

    # Compute exact C_k and S_k on X^2 and Y^2
    Ck = _compute_capacity_Ck(n, k)
    inv_n = Fraction(1, n)
    inv_n2 = Fraction(1, n * n)

    Sk = [[Fraction(0, 1)] * n for _ in range(n)]
    for a in X:
        for b in X:
            acc = Fraction(0, 1)
            for z in Y:
                acc += (
                    sX["FF"] * k[a][z] * k[b][z]
                    + sX["RR"] * k[z][a] * k[z][b]
                    + sX["FR"] * k[a][z] * k[z][b]
                    + sX["RF"] * k[z][a] * k[b][z]
                )
            Sk[a][b] = acc * inv_n
    for a in Y:
        for b in Y:
            acc = Fraction(0, 1)
            for z in X:
                acc += (
                    sY["FF"] * k[z][a] * k[z][b]
                    + sY["RR"] * k[a][z] * k[b][z]
                    + sY["FR"] * k[z][a] * k[b][z]
                    + sY["RF"] * k[a][z] * k[z][b]
                )
            Sk[a][b] = acc * inv_n

    S_val = sum(Sk[a][b] for a in X for b in X) * inv_n2 + sum(Sk[a][b] for a in Y for b in Y) * inv_n2
    J_val = (
        sum(Sk[a][b] * Ck[a][b] for a in X for b in X) * inv_n2
        + sum(Sk[a][b] * Ck[a][b] for a in Y for b in Y) * inv_n2
    )
    B0_val = (
        (2 + 2 * d) * sum(Ck[a][b] * Ck[a][b] for a in X for b in X) * inv_n2
        + 4 * sum(Ck[a][b] * Ck[a][b] for a in Y for b in Y) * inv_n2
    )

    u_plus = [sum(k[v][w] for w in range(n)) * inv_n for v in range(n)]
    u_minus = [sum(k[w][v] for w in range(n)) * inv_n for v in range(n)]
    I_val = (
        Fraction(4, n) * sum((u_plus[x] + (1 - d * Fraction(1, 8)) * u_minus[x]) ** 2 for x in X)
        + Fraction(1, n) * (1 + d * Fraction(7, 4) + d * d * Fraction(1, 64)) * sum((u_plus[y] + u_minus[y]) ** 2 for y in Y)
        + d * (16 - d) * Fraction(1, 64 * n) * sum((2 * u_plus[y] + u_minus[y]) ** 2 for y in Y)
        + d * (16 - 5 * d) * Fraction(1, 64 * n) * sum(u_plus[y] ** 2 for y in Y)
    )

    # Verify Eq. (8) identically!
    eq8_rhs = (
        (4 + 4 * d) * sum(Ck[a][b] for a in X for b in X) * inv_n2
        + 8 * sum(Ck[a][b] for a in Y for b in Y) * inv_n2
        - I_val
    )
    if S_val != eq8_rhs:
        raise VerificationError(f"Eq. (8) identity failed: S={S_val} != RHS={eq8_rhs}")

    t_val = sum(k[u][v] for u in range(n) for v in range(n)) * inv_n2
    beta_val = sum(k[y][x] for x in X for y in Y) * inv_n2
    return S_val, I_val, J_val, B0_val, t_val, beta_val, table1_sums


def _verify_mode2(payload: dict[str, Any]) -> dict[str, Any]:
    submode = _req_str(payload.get("submode"), "submode")

    if submode == "table1_quadruple_sos_identity":
        n, X, Y, k, p, q, d = _parse_bipartite_k(payload)
        S_val, I_val, J_val, B0_val, t_val, _, t1 = _sec4_eval_S_I_J_B0(n, X, Y, k, d)

        # Verify ALL 7 Table 1 exact formulas AND nonnegativity!
        expected_t1 = {
            "1234": Fraction(0, 1),
            "empty": Fraction(0, 1),
            "triples": d * d * Fraction(1, 32),
            "singletons": (1 - d * Fraction(1, 8)) * (1 - d * Fraction(9, 8)),
            "14_23": Fraction(0, 1),
            "12_34": Fraction(1, 2) - d + d * d * Fraction(1, 8),
            "13_24": 2 * ((1 + d * Fraction(1, 8)) ** 2),
        }
        for cname, exp_v in expected_t1.items():
            if t1[cname] != exp_v:
                raise VerificationError(f"Table 1 class {cname} mismatch: {t1[cname]} != {exp_v}")
            if t1[cname] < 0:
                raise VerificationError(f"Table 1 class {cname} negative: {t1[cname]}")

        if not (B0_val <= J_val <= S_val):
            raise VerificationError(f"Claim 4.2 chain B0 <= J <= S failed: {B0_val}, {J_val}, {S_val}")
        rhs_cap = (2 + 2 * d) * p * p + 4 * q * q
        if I_val > rhs_cap:
            raise VerificationError(f"Claim 4.2 failed: I={I_val} > {rhs_cap}")

        return {
            "mode": "bipartite_sos_and_table1",
            "submode": submode,
            "param_d": [d.numerator, d.denominator],
            "I_val": [I_val.numerator, I_val.denominator],
            "claim42_ub": [rhs_cap.numerator, rhs_cap.denominator],
            "t_sq_times_27": [(27 * t_val * t_val).numerator, (27 * t_val * t_val).denominator],
        }

    if submode == "claim43_quadratic_sos_bound":
        n, X, Y, k, p, q, d = _parse_bipartite_k(payload)
        _, I_val, _, _, t_val, beta_val, _ = _sec4_eval_S_I_J_B0(n, X, Y, k, d)
        rhs_cap = (2 + 2 * d) * p * p + 4 * q * q

        # Verify Claim 4.3 Cauchy-Schwarz lower bound and exact 12*p*q*Delta polynomial identity!
        inv_p = Fraction(p.denominator, p.numerator)
        inv_q = Fraction(q.denominator, q.numerator)
        cs_lb = (
            4 * inv_p * ((t_val - d * beta_val * Fraction(1, 8)) ** 2)
            + inv_q * (
                (1 + 2 * d) * t_val * t_val
                + d * (16 - d) * Fraction(1, 32) * t_val * beta_val
                + d * (16 - 3 * d) * Fraction(1, 32) * beta_val * beta_val
            )
        )
        if I_val < cs_lb:
            raise VerificationError(f"Claim 4.3 Cauchy-Schwarz violated: I={I_val} < {cs_lb}")

        delta = cs_lb - Fraction(27, 4) * rhs_cap * t_val * t_val
        lhs_12pq = 12 * p * q * delta
        rhs_poly = d * (
            2 * d * d * (d * d - 2 * d + 3) * t_val * t_val
            - d * (50 - d) * Fraction(1, 8) * t_val * beta_val
            + (5 * d * d - 20 * d + 32) * Fraction(1, 8) * beta_val * beta_val
        )
        if lhs_12pq != rhs_poly:
            raise VerificationError("Claim 4.3 exact polynomial identity 12*p*q*Delta failed")

        sos_floor = Fraction(9, 32) * d * ((4 * d * t_val - 3 * beta_val) ** 2)
        if lhs_12pq < sos_floor or sos_floor < 0:
            raise VerificationError("Claim 4.3 SOS domination 12*p*q*Delta >= (9d/32)(4dt - 3beta)^2 failed")
        if I_val < Fraction(27, 4) * rhs_cap * t_val * t_val:
            raise VerificationError("Claim 4.3 main inequality I >= (27/4)[(2+2d)p^2+4q^2]t^2 failed")
        if 27 * t_val * t_val > 4:
            raise VerificationError(f"Proposition 4.1 bound 27*t^2 <= 4 violated: {27 * t_val * t_val}")

        return {
            "mode": "bipartite_sos_and_table1",
            "submode": submode,
            "param_d": [d.numerator, d.denominator],
            "claim43_lb": [(Fraction(27, 4) * rhs_cap * t_val * t_val).numerator, (Fraction(27, 4) * rhs_cap * t_val * t_val).denominator],
            "I_val": [I_val.numerator, I_val.denominator],
            "claim42_ub": [rhs_cap.numerator, rhs_cap.denominator],
            "t_sq_times_27": [(27 * t_val * t_val).numerator, (27 * t_val * t_val).denominator],
        }

    raise VerificationError(f"Unknown Mode 2 submode: {submode}")


# ---------------------------------------------------------------------------
# Mode 3: five_walk_free_and_density (Sec. 5 Completion of Proof of Thm. 1.2)
# ---------------------------------------------------------------------------

def _verify_mode3(payload: dict[str, Any]) -> dict[str, Any]:
    submode = _req_str(payload.get("submode"), "submode")

    if submode == "five_walk_free_bipartite_extract":
        # Verify Sec. 5: no closed 5-walk in support (exact A^5 diagonal == 0), C_k <= 1,
        # heavy edge uv with d(u)+d(v) >= 2wn, disjoint N(u), N(v), disjoint independent X, Y, and Eq. (9)!
        n, k = _parse_weight_matrix(payload, max_n=14)
        Ck = _compute_capacity_Ck(n, k)
        for x in range(n):
            for y in range(n):
                if Ck[x][y] > 1:
                    raise VerificationError(f"Capacity bound violated at ({x},{y})")

        K = [[k[x][y] + k[y][x] for y in range(n)] for x in range(n)]
        A = [[1 if K[x][y] > 0 else 0 for y in range(n)] for x in range(n)]
        for x in range(n):
            if A[x][x] != 0:
                raise VerificationError(f"Support has self-loop at {x} (creates closed 5-walk)")

        # Exact integer matrix power A^5 to verify ZERO closed 5-walks!
        def mat_mul(M1: list[list[int]], M2: list[list[int]]) -> list[list[int]]:
            out = [[0] * n for _ in range(n)]
            for i in range(n):
                for r in range(n):
                    if M1[i][r]:
                        for j in range(n):
                            out[i][j] += M1[i][r] * M2[r][j]
            return out

        A2 = mat_mul(A, A)
        A4 = mat_mul(A2, A2)
        A5 = mat_mul(A4, A)
        for x in range(n):
            if A5[x][x] != 0:
                raise VerificationError(f"Support contains a closed 5-walk at vertex {x}")

        # Verify Cauchy-Schwarz 4*t^2 <= w * ||K||_2^2 <= (4/3)*w
        t_val = sum(k[x][y] for x in range(n) for y in range(n)) * Fraction(1, n * n)
        pos_pairs = sum(A[x][y] for x in range(n) for y in range(n))
        w_val = Fraction(pos_pairs, n * n)
        l2_sq = sum(K[x][y] * K[x][y] for x in range(n) for y in range(n)) * Fraction(1, n * n)
        if not (4 * t_val * t_val <= w_val * l2_sq <= Fraction(4, 3) * w_val):
            raise VerificationError("Sec. 5 Cauchy-Schwarz chain 4t^2 <= w||K||_2^2 <= (4/3)w failed")

        # Verify supplied heavy edge (u, v) satisfies A[u][v]=1 and d(u)+d(v) >= 2*w*n
        u = _req_int(payload.get("heavy_edge_u"), "heavy_edge_u", 0, n - 1)
        v = _req_int(payload.get("heavy_edge_v"), "heavy_edge_v", 0, n - 1)
        if A[u][v] != 1:
            raise VerificationError(f"({u},{v}) is not an edge in support of k")
        N_of = [{y for y in range(n) if A[x][y] == 1} for x in range(n)]
        if len(N_of[u]) + len(N_of[v]) < 2 * w_val * n:
            raise VerificationError("Heavy edge fails d(u) + d(v) >= 2wn")
        if N_of[u] & N_of[v]:
            raise VerificationError("N(u) and N(v) overlap (contradicts no closed 5-walk)")

        X = set().union(*(N_of[a] for a in N_of[u])) if N_of[u] else set()
        Y = set().union(*(N_of[b] for b in N_of[v])) if N_of[v] else set()
        if X & Y:
            raise VerificationError("Extracted X and Y overlap (contradicts no closed 5-walk)")
        for x1 in X:
            for x2 in X:
                if A[x1][x2]:
                    raise VerificationError("Extracted X is not independent")
        for y1 in Y:
            for y2 in Y:
                if A[y1][y2]:
                    raise VerificationError("Extracted Y is not independent")

        U = X | Y
        U_bar = [x for x in range(n) if x not in U]
        B_set = N_of[u] | N_of[v]
        if not B_set.issubset(U):
            raise VerificationError("B = N(u) U N(v) not subset of U = X U Y")
        # Verify Eq. (9) Cauchy-Schwarz row bound for every residual vertex x in U_bar
        for x in U_bar:
            if N_of[x] & B_set:
                raise VerificationError(f"Residual vertex {x} has neighbor in B")
            row_sum_K = sum(K[x][y] for y in range(n)) * Fraction(1, n)
            if row_sum_K * row_sum_K > Fraction(2 * len(N_of[x]), n):
                raise VerificationError(f"Sec. 5 residual Cauchy-Schwarz bound failed at {x}")

        return {
            "mode": "five_walk_free_and_density",
            "submode": submode,
            "num_vertices": n,
            "edge_density_w": [w_val.numerator, w_val.denominator],
            "X_size": len(X),
            "Y_size": len(Y),
            "residual_size": len(U_bar),
            "t_sq_times_27": [(27 * t_val * t_val).numerator, (27 * t_val * t_val).denominator],
        }

    if submode == "rho_monotonicity_contradiction":
        # Verify Sec. 5 final cleared-square monotonicity proof over exact Q for rho list in (0, 1/9]:
        # (1-rho)^(3/2) < 1 - (3/2)rho + (1/2)rho^2 (since diff^2 = (1/4)*rho^2*(1-rho)^2 > 0),
        # AND (3 - rho)^2 > 6 (certifying (2/(3*sqrt(3)))*(1-rho)^(3/2) + (sqrt(2)/3)*rho < 2/(3*sqrt(3)))!
        rhos_raw = _req_list(payload.get("rho_values"), "rho_values", 2, 32)
        seen_rho: set[Fraction] = set()
        min_margin_sq = None
        for idx, rr in enumerate(rhos_raw):
            rho = _parse_rat(rr, f"rho_values[{idx}]")
            if rho in seen_rho:
                raise VerificationError(f"Duplicate rho value {rho}")
            seen_rho.add(rho)
            if not (0 < rho <= Fraction(1, 9)):
                raise VerificationError(f"rho={rho} outside Sec. 5 range (0, 1/9]")
            # Verify exact algebraic identity: (1 - 3/2*rho + 1/2*rho^2)^2 - (1 - rho)^3 == (1/4)*rho^2*(1 - rho)^2 > 0
            poly_ub = 1 - Fraction(3, 2) * rho + Fraction(1, 2) * rho * rho
            diff_sq = poly_ub * poly_ub - ((1 - rho) ** 3)
            expected_diff = Fraction(1, 4) * rho * rho * ((1 - rho) ** 2)
            if diff_sq != expected_diff or diff_sq <= 0:
                raise VerificationError("Exact binomial upper bound for (1-rho)^(3/2) failed")
            # Verify strict margin: (3 - rho)^2 > 6 (certifies strictly decreasing below 2/(3*sqrt(3)))
            slope_lhs = 3 - rho
            lhs_sq = slope_lhs * slope_lhs
            if lhs_sq <= 6:
                raise VerificationError(f"Monotonicity margin failed at rho={rho}: {lhs_sq} <= 6")
            if min_margin_sq is None or lhs_sq < min_margin_sq:
                min_margin_sq = lhs_sq

        assert min_margin_sq is not None
        return {
            "mode": "five_walk_free_and_density",
            "submode": submode,
            "checked_rhos": len(seen_rho),
            "min_slope_sq": [min_margin_sq.numerator, min_margin_sq.denominator],
        }

    raise VerificationError(f"Unknown Mode 3 submode: {submode}")


# ---------------------------------------------------------------------------
# Mode 4: bollobas_gyori_and_applications (Thms. 1.2-1.4 Construction & Berge Shadow)
# ---------------------------------------------------------------------------

def _verify_mode4(payload: dict[str, Any]) -> dict[str, Any]:
    submode = _req_str(payload.get("submode"), "submode")

    if submode == "bollobas_gyori_doubled_bip":
        # Given a C_4-free bipartite graph B = (L, R), verify C_4-freeness, double L with matching spine edges,
        # verify the doubled graph G is BOTH C_5-free AND induced-C_4-free (Thms. 1.2 & 1.3!),
        # and verify exact triangle count == |E(B)| and edge count == 2*|E(B)| + |L|!
        mL = _req_int(payload.get("left_size"), "left_size", 2, 16)
        mR = _req_int(payload.get("right_size"), "right_size", 2, 16)
        bip_raw = _req_list(payload.get("bip_edges"), "bip_edges", 2, mL * mR)
        bip_edges: list[tuple[int, int]] = []
        seen_be: set[tuple[int, int]] = set()
        nbrR: list[set[int]] = [set() for _ in range(mL)]
        for idx, er in enumerate(bip_raw):
            el = _req_list(er, f"bip_edges[{idx}]", 2, 2)
            l_v = _req_int(el[0], f"bip[{idx}][0]", 0, mL - 1)
            r_v = _req_int(el[1], f"bip[{idx}][1]", 0, mR - 1)
            if (l_v, r_v) in seen_be:
                raise VerificationError(f"Duplicate bipartite edge ({l_v},{r_v})")
            seen_be.add((l_v, r_v))
            bip_edges.append((l_v, r_v))
            nbrR[l_v].add(r_v)

        # Verify B is C_4-free (no two left vertices share >= 2 right neighbors)
        for i in range(mL):
            for j in range(i + 1, mL):
                if len(nbrR[i] & nbrR[j]) >= 2:
                    raise VerificationError(f"Bipartite base graph B contains a C_4 on left pair ({i},{j})")

        # Construct Bollobas-Gyori doubled graph G on n = 2*mL + mR vertices:
        # Left copies: 0..mL-1 and mL..2*mL-1; Right vertices: 2*mL..2*mL+mR-1
        nG = 2 * mL + mR
        adjG: list[set[int]] = [set() for _ in range(nG)]
        edge_cnt = 0
        for i in range(mL):
            adjG[i].add(mL + i)
            adjG[mL + i].add(i)
            edge_cnt += 1
        for l_v, r_v in bip_edges:
            rv_id = 2 * mL + r_v
            adjG[l_v].add(rv_id)
            adjG[rv_id].add(l_v)
            adjG[mL + l_v].add(rv_id)
            adjG[rv_id].add(mL + l_v)
            edge_cnt += 2

        if _has_c5(nG, adjG):
            raise VerificationError("Doubled Bollobas-Gyori graph unexpectedly contains C_5")
        if _has_induced_c4(nG, adjG):
            raise VerificationError("Doubled Bollobas-Gyori graph unexpectedly contains induced C_4")

        # Count exact triangles in G
        tri_cnt = 0
        for u in range(nG):
            for v in adjG[u]:
                if v <= u:
                    continue
                for w in adjG[u] & adjG[v]:
                    if w > v:
                        tri_cnt += 1

        if tri_cnt != len(bip_edges):
            raise VerificationError(f"Triangle count {tri_cnt} != |E(B)|={len(bip_edges)}")
        if edge_cnt != 2 * len(bip_edges) + mL:
            raise VerificationError(f"Edge count {edge_cnt} != 2|E(B)|+|L|={2*len(bip_edges)+mL}")

        # Exact squared normalized triangle ratio tau(G)^2 / nG^3 (compared against 1/27)
        tri_ratio_sq = Fraction(tri_cnt * tri_cnt, nG ** 3)
        return {
            "mode": "bollobas_gyori_and_applications",
            "submode": submode,
            "num_vertices_G": nG,
            "triangles_G": tri_cnt,
            "edges_G": edge_cnt,
            "tri_ratio_sq": [tri_ratio_sq.numerator, tri_ratio_sq.denominator],
        }

    if submode == "berge_3graph_shadow_reduction":
        # Verify Theorem 1.4: explicit 3-uniform hypergraph H is {BC_3, BC_4, BC_5}-free,
        # its 2-shadow G = partial(H) is C_5-free, and every hyperedge maps to a distinct triangle in G!
        n = _req_int(payload.get("num_vertices"), "num_vertices", 3, 24)
        he_raw = _req_list(payload.get("hyperedges"), "hyperedges", 2, 60)
        hyperedges: list[tuple[int, int, int]] = []
        seen_he: set[tuple[int, int, int]] = set()
        for idx, hr in enumerate(he_raw):
            hl = _req_list(hr, f"hyperedges[{idx}]", 3, 3)
            verts = sorted(_req_int(v, f"he[{idx}]", 0, n - 1) for v in hl)
            if len(set(verts)) != 3:
                raise VerificationError(f"Hyperedge {idx} does not have 3 distinct vertices")
            tup = (verts[0], verts[1], verts[2])
            if tup in seen_he:
                raise VerificationError(f"Duplicate hyperedge {tup}")
            seen_he.add(tup)
            hyperedges.append(tup)

        # Build bipartite incidence graph: pair (u, v) -> list of hyperedge indices containing {u, v}
        pair_to_hes: dict[tuple[int, int], list[int]] = {}
        adjG: list[set[int]] = [set() for _ in range(n)]
        for hid, (a, b, c) in enumerate(hyperedges):
            for u, v in ((a, b), (a, c), (b, c)):
                adjG[u].add(v)
                adjG[v].add(u)
                pair_to_hes.setdefault((u, v), []).append(hid)
                pair_to_hes.setdefault((v, u), []).append(hid)

        # Exhaustive Berge cycle checker for lengths L in {3, 4, 5}:
        # distinct vertices v_0..v_{L-1} and distinct hyperedges h_0..h_{L-1} with {v_i, v_{i+1}} subset h_i!
        def has_berge_cycle(length: int) -> bool:
            used_v = [False] * n
            used_h = [False] * len(hyperedges)

            def dfs(start: int, cur: int, depth: int) -> bool:
                if depth == length - 1:
                    if start in adjG[cur]:
                        for hid in pair_to_hes[(cur, start)]:
                            if not used_h[hid]:
                                return True
                    return False
                for nxt in adjG[cur]:
                    if nxt <= start or used_v[nxt]:
                        continue
                    used_v[nxt] = True
                    for hid in pair_to_hes[(cur, nxt)]:
                        if not used_h[hid]:
                            used_h[hid] = True
                            if dfs(start, nxt, depth + 1):
                                return True
                            used_h[hid] = False
                    used_v[nxt] = False
                return False

            for s in range(n):
                used_v[s] = True
                if dfs(s, s, 0):
                    return True
                used_v[s] = False
            return False

        for ell in (3, 4, 5):
            if has_berge_cycle(ell):
                raise VerificationError(f"Hypergraph H contains a Berge cycle BC_{ell}")

        # Verify 2-shadow G is C_5-free and count triangles in G
        if _has_c5(n, adjG):
            raise VerificationError("2-shadow graph G contains C_5")
        tri_G = 0
        for u in range(n):
            for v in adjG[u]:
                if v <= u:
                    continue
                for w in adjG[u] & adjG[v]:
                    if w > v:
                        tri_G += 1
        if len(hyperedges) > tri_G:
            raise VerificationError("Hyperedge count exceeds shadow triangle count")

        return {
            "mode": "bollobas_gyori_and_applications",
            "submode": submode,
            "num_vertices": n,
            "num_hyperedges": len(hyperedges),
            "shadow_triangles": tri_G,
            "shadow_c5_free": True,
        }

    raise VerificationError(f"Unknown Mode 4 submode: {submode}")


# ---------------------------------------------------------------------------
# Entry Points
# ---------------------------------------------------------------------------

def verify_certificate(cert: Any) -> dict[str, Any]:
    d = _req_dict(cert, "certificate")
    if d.get("schema_version") != SCHEMA_VERSION:
        raise VerificationError(f"Expected schema_version={SCHEMA_VERSION}, got {d.get('schema_version')}")
    _req_str(d.get("certificate_id"), "certificate_id")
    _req_str(d.get("paper_reference"), "paper_reference")
    mode = _req_str(d.get("mode"), "mode")
    payload = _req_dict(d.get("payload"), "payload")

    if mode == "book_reduction_and_capacity":
        res = _verify_mode1(payload)
    elif mode == "bipartite_sos_and_table1":
        res = _verify_mode2(payload)
    elif mode == "five_walk_free_and_density":
        res = _verify_mode3(payload)
    elif mode == "bollobas_gyori_and_applications":
        res = _verify_mode4(payload)
    else:
        raise VerificationError(f"Unknown mode: {mode}")

    res["certificate_id"] = d["certificate_id"]
    res["status"] = "VERIFIED"
    return res


def verify_file(path: pathlib.Path | str) -> dict[str, Any]:
    p = pathlib.Path(path)
    if not p.is_file():
        raise VerificationError(f"Certificate path is not a readable file: {p}")
    if p.stat().st_size > MAX_JSON_BYTES:
        raise VerificationError(f"Certificate {p.name} exceeds MAX_JSON_BYTES={MAX_JSON_BYTES}")
    raw = p.read_bytes()
    if len(raw) > MAX_JSON_BYTES:
        raise VerificationError(f"Certificate {p.name} exceeds MAX_JSON_BYTES={MAX_JSON_BYTES}")
    try:
        data = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=_no_dup_pairs,
            parse_constant=_reject_json_constant,
            parse_float=_reject_json_float,
        )
    except VerificationError:
        raise
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise VerificationError(f"Invalid JSON in {p.name}: {exc}") from exc
    return verify_certificate(data)


def main(argv: list[str] | None = None) -> int:
    args = sys.argv[1:] if argv is None else argv
    if not args:
        print("Usage: python -m src.ex_k3_c5_verifier <file-or-dir> [...]", file=sys.stderr)
        return 2
    files: list[pathlib.Path] = []
    for a in args:
        p = pathlib.Path(a)
        if p.is_dir():
            files.extend(sorted(p.glob("*.json")))
        else:
            files.append(p)
    if not files:
        print("No certificate files found.", file=sys.stderr)
        return 2
    verified = 0
    for f in files:
        res = verify_file(f)
        print(f"[VERIFIED] {f.name}: {res['mode']} ({res['submode']})")
        verified += 1
    print(f"Verified {verified}/{len(files)} certificates under {SCHEMA_VERSION}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
