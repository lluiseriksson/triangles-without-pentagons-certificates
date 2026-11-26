"""
Generate the 16 canonical EX-K3-C5-CERT-1.0 certificates (C01..C16) for
paper75-triangles-without-pentagons-certificates and verify every single one
through src.ex_k3_c5_verifier.verify_file.
"""

from __future__ import annotations

import json
import pathlib
import sys
from fractions import Fraction

ROOT = pathlib.Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.ex_k3_c5_verifier import SCHEMA_VERSION, verify_file

CERTS_DIR = ROOT / "certificates"


def _r(num: int, den: int = 1) -> list[int]:
    f = Fraction(num, den)
    return [f.numerator, f.denominator]


def _zero_mat(n: int) -> list[list[list[int]]]:
    return [[[0, 1] for _ in range(n)] for _ in range(n)]


def _pg2_bipartite(q: int) -> tuple[int, int, list[list[int]]]:
    """Exact projective plane PG(2, q) point-line incidence bipartite graph (C_4-free)."""
    # Points in P^2(F_q): normalized tuples (x, y, z) with first nonzero entry == 1
    pts: list[tuple[int, int, int]] = []
    for x in range(q):
        for y in range(q):
            for z in range(q):
                if (x, y, z) == (0, 0, 0):
                    continue
                first_nz = x if x != 0 else (y if y != 0 else z)
                if first_nz == 1:
                    pts.append((x, y, z))
    lines = list(pts)
    edges: list[list[int]] = []
    for li, (a, b, c) in enumerate(lines):
        for pi, (x, y, z) in enumerate(pts):
            if (a * x + b * y + c * z) % q == 0:
                edges.append([li, pi])
    return len(lines), len(pts), edges


def build_certificates() -> list[tuple[str, dict]]:
    certs: list[tuple[str, dict]] = []

    # ------------------------------------------------------------------
    # Mode 1a: book_block_orientation_and_cap (Prop. 2.6 & Lemma 2.8)
    # ------------------------------------------------------------------
    # C01: n=10 C_5-free graph with 1 K_4 block ({0,1,2,3}) + 2 book blocks
    # Spine (3,4) with 3 pages {5,6,7}, and spine (4,8) with 1 page {9}.
    c01_edges = [
        [0, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 3],
        [3, 4],
        [3, 5], [4, 5], [3, 6], [4, 6], [3, 7], [4, 7],
        [4, 8], [4, 9], [8, 9],
    ]
    certs.append((
        "C01_book_k4_blocks_n10.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C01_book_k4_blocks_n10",
            "paper_reference": "Cui-Gyori-Zhang-Zhu (arXiv:2611.33685v1), Sec. 2 Prop. 2.6 & Lemma 2.8",
            "mode": "book_reduction_and_capacity",
            "payload": {
                "submode": "book_block_orientation_and_cap",
                "num_vertices": 10,
                "edges": c01_edges,
            },
        },
    ))

    # C02: n=14 C_5-free graph: Bollobas-Gyori doubled tree (3 books, 7 triangles) + K_4 at cut-vertex 9
    # Spines: (0,3) pages {6,7,13}; (1,4) pages {7,8}; (2,5) pages {8,9}; K_4 on {9,10,11,12}
    c02_edges = [
        [0, 3], [1, 4], [2, 5],
        [0, 6], [3, 6], [0, 7], [3, 7], [0, 13], [3, 13],
        [1, 7], [4, 7], [1, 8], [4, 8],
        [2, 8], [5, 8], [2, 9], [5, 9],
        [9, 10], [9, 11], [9, 12], [10, 11], [10, 12], [11, 12],
    ]
    certs.append((
        "C02_doubled_tree_k4_n14.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C02_doubled_tree_k4_n14",
            "paper_reference": "Cui-Gyori-Zhang-Zhu (arXiv:2611.33685v1), Sec. 2 Prop. 2.6 & Lemma 2.8",
            "mode": "book_reduction_and_capacity",
            "payload": {
                "submode": "book_block_orientation_and_cap",
                "num_vertices": 14,
                "edges": c02_edges,
            },
        },
    ))

    # ------------------------------------------------------------------
    # Mode 1b: capacity_l2_and_row_bounds (Lemma 2.5 Eq. (1))
    # ------------------------------------------------------------------
    # C03: Near-tight extremal Bollobas-Gyori discretization on n=3 (X={0,1}, Y={2}, k[x][2]=71/41)
    # 71^2 / (3 * 41^2) = 5041/5043 < 1; ||K||_2^2 = 20164/15129 ~ 1.33280 vs 4/3!
    k03 = _zero_mat(3)
    k03[0][2] = _r(71, 41)
    k03[1][2] = _r(71, 41)
    certs.append((
        "C03_extremal_bip_capacity_n3.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C03_extremal_bip_capacity_n3",
            "paper_reference": "Cui-Gyori-Zhang-Zhu (arXiv:2611.33685v1), Sec. 2 Lemma 2.5 Eq. (1)",
            "mode": "book_reduction_and_capacity",
            "payload": {
                "submode": "capacity_l2_and_row_bounds",
                "num_vertices": 3,
                "weight_matrix_k": k03,
            },
        },
    ))

    # C04: Non-bipartite mixed bidirectional directed weight matrix on n=6 (tests all 4 terms of C_k)
    k04 = _zero_mat(6)
    # Directed 6-cycle + chords with asymmetric forward/reverse weights keeping C_k <= 1
    arcs04 = [
        (0, 1, (3, 4)), (1, 2, (2, 3)), (2, 3, (3, 4)),
        (3, 4, (2, 3)), (4, 5, (3, 4)), (5, 0, (2, 3)),
        (0, 3, (1, 2)), (3, 0, (1, 4)), (1, 4, (1, 2)), (5, 2, (1, 3)),
    ]
    for u, v, (a, b) in arcs04:
        k04[u][v] = _r(a, b)
    certs.append((
        "C04_mixed_bidirectional_capacity_n6.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C04_mixed_bidirectional_capacity_n6",
            "paper_reference": "Cui-Gyori-Zhang-Zhu (arXiv:2611.33685v1), Sec. 2 Lemma 2.5 Eq. (1)",
            "mode": "book_reduction_and_capacity",
            "payload": {
                "submode": "capacity_l2_and_row_bounds",
                "num_vertices": 6,
                "weight_matrix_k": k04,
            },
        },
    ))

    # ------------------------------------------------------------------
    # Mode 2a: table1_quadruple_sos_identity (Sec. 4 Table 1, Eq. (8), Claim 4.2)
    # ------------------------------------------------------------------
    # C05: n=4, X={0,1}, Y={2,3}, p=1/2, q=1/2, d=1/2; all 4 orientation types (FF, RR, FR, RF) active!
    k05 = _zero_mat(4)
    k05[0][2] = _r(3, 4)
    k05[0][3] = _r(1, 2)
    k05[1][2] = _r(1, 2)
    k05[1][3] = _r(3, 4)
    k05[2][0] = _r(1, 4)
    k05[2][1] = _r(1, 3)
    k05[3][0] = _r(1, 3)
    k05[3][1] = _r(1, 4)
    certs.append((
        "C05_table1_balanced_d1_2_n4.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C05_table1_balanced_d1_2_n4",
            "paper_reference": "Cui-Gyori-Zhang-Zhu (arXiv:2611.33685v1), Sec. 4 Table 1, Eq. (8) & Claim 4.2",
            "mode": "bipartite_sos_and_table1",
            "payload": {
                "submode": "table1_quadruple_sos_identity",
                "num_vertices": 4,
                "part_X": [0, 1],
                "weight_matrix_k": k05,
            },
        },
    ))

    # C06: n=12, |X|=7, |Y|=5, p=7/12, q=5/12, d=1/4; asymmetric heterogeneous bipartite kernel
    k06 = _zero_mat(12)
    for x in range(7):
        for y in range(7, 12):
            k06[x][y] = _r(5, 6) if (x + y) % 2 == 0 else _r(2, 3)
            k06[y][x] = _r(1, 5) if (x + y) % 3 == 0 else _r(1, 10)
    certs.append((
        "C06_table1_asymmetric_d1_4_n12.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C06_table1_asymmetric_d1_4_n12",
            "paper_reference": "Cui-Gyori-Zhang-Zhu (arXiv:2611.33685v1), Sec. 4 Table 1, Eq. (8) & Claim 4.2",
            "mode": "bipartite_sos_and_table1",
            "payload": {
                "submode": "table1_quadruple_sos_identity",
                "num_vertices": 12,
                "part_X": list(range(7)),
                "weight_matrix_k": k06,
            },
        },
    ))

    # ------------------------------------------------------------------
    # Mode 2b: claim43_quadratic_sos_bound (Sec. 4 Claim 4.3 & Prop. 4.1)
    # ------------------------------------------------------------------
    # C07: n=8, |X|=5, |Y|=3, p=5/8, q=3/8, d=1/8; high forward density near extremal p=2/3 boundary!
    # With k[x][y] = 3/2 and k[y][x] = 1/20: C_k(X^2) = 5763/6400 < 1, C_k(Y^2) = 511/640 < 1.
    k07 = _zero_mat(8)
    for x in range(5):
        for y in range(5, 8):
            k07[x][y] = _r(3, 2)
            k07[y][x] = _r(1, 20)
    certs.append((
        "C07_claim43_near_extremal_d1_8_n8.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C07_claim43_near_extremal_d1_8_n8",
            "paper_reference": "Cui-Gyori-Zhang-Zhu (arXiv:2611.33685v1), Sec. 4 Claim 4.3 & Prop. 4.1",
            "mode": "bipartite_sos_and_table1",
            "payload": {
                "submode": "claim43_quadratic_sos_bound",
                "num_vertices": 8,
                "part_X": [0, 1, 2, 3, 4],
                "weight_matrix_k": k07,
            },
        },
    ))

    # C08: n=7, |X|=4, |Y|=3, p=4/7, q=3/7, d=2/7; non-uniform mixed forward/reverse kernel
    k08 = _zero_mat(7)
    for x in range(4):
        for y in range(4, 7):
            k08[x][y] = _r(6, 5) if x < 2 else _r(4, 5)
            k08[y][x] = _r(1, 4) if y == 4 else _r(1, 8)
    certs.append((
        "C08_claim43_heterogeneous_d2_7_n7.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C08_claim43_heterogeneous_d2_7_n7",
            "paper_reference": "Cui-Gyori-Zhang-Zhu (arXiv:2611.33685v1), Sec. 4 Claim 4.3 & Prop. 4.1",
            "mode": "bipartite_sos_and_table1",
            "payload": {
                "submode": "claim43_quadratic_sos_bound",
                "num_vertices": 7,
                "part_X": [0, 1, 2, 3],
                "weight_matrix_k": k08,
            },
        },
    ))

    # ------------------------------------------------------------------
    # Mode 3a: five_walk_free_bipartite_extract (Sec. 5 A^5=0, heavy edge, Eq. (9))
    # ------------------------------------------------------------------
    # C09: n=6, K_{4,2} near-extremal 5-walk-free kernel with k[x][y] = 71/41 (27*t^2 ~ 3.9984!)
    k09 = _zero_mat(6)
    for x in range(4):
        for y in (4, 5):
            k09[x][y] = _r(71, 41)
    certs.append((
        "C09_five_walk_free_near_tight_n6.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C09_five_walk_free_near_tight_n6",
            "paper_reference": "Cui-Gyori-Zhang-Zhu (arXiv:2611.33685v1), Sec. 5 Bipartite Extraction & Cauchy-Schwarz",
            "mode": "five_walk_free_and_density",
            "payload": {
                "submode": "five_walk_free_bipartite_extract",
                "num_vertices": 6,
                "weight_matrix_k": k09,
                "heavy_edge_u": 0,
                "heavy_edge_v": 4,
            },
        },
    ))

    # C10: n=10, K_{5,3} main bipartite block + disjoint residual edge (8,9) in U_bar (non-vacuous Eq. (9)!)
    k10 = _zero_mat(10)
    for x in range(5):
        for y in (5, 6, 7):
            k10[x][y] = _r(3, 2)
    k10[8][9] = _r(1, 2)
    k10[9][8] = _r(1, 3)
    certs.append((
        "C10_five_walk_free_with_residual_n10.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C10_five_walk_free_with_residual_n10",
            "paper_reference": "Cui-Gyori-Zhang-Zhu (arXiv:2611.33685v1), Sec. 5 Residual Deletion Eq. (9)",
            "mode": "five_walk_free_and_density",
            "payload": {
                "submode": "five_walk_free_bipartite_extract",
                "num_vertices": 10,
                "weight_matrix_k": k10,
                "heavy_edge_u": 0,
                "heavy_edge_v": 5,
            },
        },
    ))

    # ------------------------------------------------------------------
    # Mode 3b: rho_monotonicity_contradiction (Sec. 5 Exact Rational Monotonicity)
    # ------------------------------------------------------------------
    certs.append((
        "C11_rho_grid_interior.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C11_rho_grid_interior",
            "paper_reference": "Cui-Gyori-Zhang-Zhu (arXiv:2611.33685v1), Sec. 5 Final Contradiction on (0, 1/9]",
            "mode": "five_walk_free_and_density",
            "payload": {
                "submode": "rho_monotonicity_contradiction",
                "rho_values": [
                    _r(1, 100), _r(1, 50), _r(1, 36), _r(1, 27),
                    _r(1, 18), _r(1, 12), _r(1, 10), _r(1, 9),
                ],
            },
        },
    ))

    certs.append((
        "C12_rho_boundary_refinement.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C12_rho_boundary_refinement",
            "paper_reference": "Cui-Gyori-Zhang-Zhu (arXiv:2611.33685v1), Sec. 5 Boundary Refinement near rho=0 and 1/9",
            "mode": "five_walk_free_and_density",
            "payload": {
                "submode": "rho_monotonicity_contradiction",
                "rho_values": [
                    _r(1, 1000), _r(1, 500), _r(1, 200), _r(1, 128), _r(1, 64),
                    _r(1, 32), _r(1, 16), _r(1, 11), _r(10, 99), _r(1, 9),
                ],
            },
        },
    ))

    # ------------------------------------------------------------------
    # Mode 4a: bollobas_gyori_doubled_bip (Thms. 1.2 & 1.3 Lower-Bound Constructions)
    # ------------------------------------------------------------------
    mL2, mR2, bip2 = _pg2_bipartite(2)
    certs.append((
        "C13_bollobas_gyori_fano_pg22.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C13_bollobas_gyori_fano_pg22",
            "paper_reference": "Cui-Gyori-Zhang-Zhu (arXiv:2611.33685v1), Thms. 1.2 & 1.3 Bollobas-Gyori Doubled PG(2,2)",
            "mode": "bollobas_gyori_and_applications",
            "payload": {
                "submode": "bollobas_gyori_doubled_bip",
                "left_size": mL2,
                "right_size": mR2,
                "bip_edges": bip2,
            },
        },
    ))

    mL3, mR3, bip3 = _pg2_bipartite(3)
    certs.append((
        "C14_bollobas_gyori_pg23.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C14_bollobas_gyori_pg23",
            "paper_reference": "Cui-Gyori-Zhang-Zhu (arXiv:2611.33685v1), Thms. 1.2 & 1.3 Bollobas-Gyori Doubled PG(2,3)",
            "mode": "bollobas_gyori_and_applications",
            "payload": {
                "submode": "bollobas_gyori_doubled_bip",
                "left_size": mL3,
                "right_size": mR3,
                "bip_edges": bip3,
            },
        },
    ))

    # ------------------------------------------------------------------
    # Mode 4b: berge_3graph_shadow_reduction (Thm. 1.4 3-Uniform Berge-Cycle Conjecture)
    # ------------------------------------------------------------------
    # C15: Triangle-3-graph of doubled PG(2,2): n=21 vertices, 21 hyperedges, {BC_3, BC_4, BC_5}-free!
    hes15 = [[l_v, mL2 + l_v, 2 * mL2 + r_v] for (l_v, r_v) in bip2]
    certs.append((
        "C15_berge_3graph_fano_doubled.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C15_berge_3graph_fano_doubled",
            "paper_reference": "Cui-Gyori-Zhang-Zhu (arXiv:2611.33685v1), Thm. 1.4 {BC_3,BC_4,BC_5}-Free Extremal 3-Graph",
            "mode": "bollobas_gyori_and_applications",
            "payload": {
                "submode": "berge_3graph_shadow_reduction",
                "num_vertices": 2 * mL2 + mR2,
                "hyperedges": hes15,
            },
        },
    ))

    # C16: Strictly linear girth-6 3-uniform hypergraph on n=24 vertices (6-cycle ring + 6 pendant triangles = 12 hyperedges)
    # Ring vertices 0..5, ring apexes 6..11, pendant pairs (12,13)..(22,23) attached at 0..5
    hes16 = [
        [0, 1, 6], [1, 2, 7], [2, 3, 8], [3, 4, 9], [4, 5, 10], [5, 0, 11],
        [0, 12, 13], [1, 14, 15], [2, 16, 17], [3, 18, 19], [4, 20, 21], [5, 22, 23],
    ]
    certs.append((
        "C16_berge_3graph_linear_girth6.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C16_berge_3graph_linear_girth6",
            "paper_reference": "Cui-Gyori-Zhang-Zhu (arXiv:2611.33685v1), Thm. 1.4 Linear Girth-6 3-Graph Shadow Reduction",
            "mode": "bollobas_gyori_and_applications",
            "payload": {
                "submode": "berge_3graph_shadow_reduction",
                "num_vertices": 24,
                "hyperedges": hes16,
            },
        },
    ))

    return certs


def main() -> int:
    CERTS_DIR.mkdir(parents=True, exist_ok=True)
    certs = build_certificates()
    for fname, obj in certs:
        out_path = CERTS_DIR / fname
        out_path.write_text(json.dumps(obj, indent=2) + "\n", encoding="utf-8")
        res = verify_file(out_path)
        print(f"[OK] {fname}: {res}")
    print(f"Generated and verified {len(certs)} certificates in {CERTS_DIR}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
