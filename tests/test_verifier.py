"""
Comprehensive unit, adversarial forgery, security, and zero-float AST audit tests
for EX-K3-C5-CERT-1.0 (src/ex_k3_c5_verifier.py).
"""

from __future__ import annotations

import ast
import copy
import json
import pathlib
import sys

import pytest

ROOT = pathlib.Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.ex_k3_c5_verifier import MAX_JSON_BYTES, SCHEMA_VERSION, VerificationError, main, verify_certificate, verify_file

CERTS_DIR = ROOT / "certificates"
VERIFIER_PATH = ROOT / "src" / "ex_k3_c5_verifier.py"


def _load(name: str) -> dict:
    return json.loads((CERTS_DIR / name).read_text(encoding="utf-8"))


# ---------------------------------------------------------------------------
# 1. Canonical 16-Certificate Verification + CLI
# ---------------------------------------------------------------------------

CANONICAL_FILES = sorted(p.name for p in CERTS_DIR.glob("C*.json"))


def test_canonical_count_is_16() -> None:
    assert len(CANONICAL_FILES) == 16


@pytest.mark.parametrize("fname", CANONICAL_FILES)
def test_canonical_certificate_verifies(fname: str) -> None:
    res = verify_file(CERTS_DIR / fname)
    assert res["status"] == "VERIFIED"
    assert res["certificate_id"] == fname.removesuffix(".json")


def test_cli_directory_mode_exits_zero() -> None:
    assert main([str(CERTS_DIR)]) == 0


def test_cli_no_args_returns_two() -> None:
    assert main([]) == 2


def test_cli_empty_dir_returns_two(tmp_path: pathlib.Path) -> None:
    assert main([str(tmp_path)]) == 2


# ---------------------------------------------------------------------------
# 2. Zero-Float AST & Import Audit on Verifier Source
# ---------------------------------------------------------------------------

def test_verifier_has_zero_floats_no_truediv_no_math_numpy() -> None:
    src = VERIFIER_PATH.read_text(encoding="utf-8")
    tree = ast.parse(src)
    forbidden_mods = {"math", "cmath", "numpy", "scipy", "decimal"}
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and isinstance(node.value, float):
            pytest.fail(f"Float literal found in verifier: {node.value}")
        if isinstance(node, (ast.Div,)):
            pytest.fail("True division operator (/) found in verifier")
        if isinstance(node, ast.AugAssign) and isinstance(node.op, ast.Div):
            pytest.fail("In-place true division (/=) found in verifier")
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "float":
            pytest.fail("float() call found in verifier")
        if isinstance(node, ast.Import):
            for alias in node.names:
                assert alias.name.split(".")[0] not in forbidden_mods
        if isinstance(node, ast.ImportFrom) and node.module:
            assert node.module.split(".")[0] not in forbidden_mods


# ---------------------------------------------------------------------------
# 3. Schema, Security, Duplicate-Key, Float-Literal & Bounds Hardening
# ---------------------------------------------------------------------------

def test_reject_wrong_schema() -> None:
    c = _load("C01_book_k4_blocks_n10.json")
    c["schema_version"] = "WRONG-1.0"
    with pytest.raises(VerificationError, match="schema_version"):
        verify_certificate(c)


def test_reject_unknown_mode() -> None:
    c = _load("C01_book_k4_blocks_n10.json")
    c["mode"] = "nonexistent_mode"
    with pytest.raises(VerificationError, match="Unknown mode"):
        verify_certificate(c)


def test_reject_unknown_submodes() -> None:
    for fname in (
        "C01_book_k4_blocks_n10.json",
        "C05_table1_balanced_d1_2_n4.json",
        "C09_five_walk_free_near_tight_n6.json",
        "C13_bollobas_gyori_fano_pg22.json",
    ):
        c = _load(fname)
        c["payload"]["submode"] = "bogus_submode"
        with pytest.raises(VerificationError, match="Unknown Mode"):
            verify_certificate(c)


def test_reject_float_literal_in_json(tmp_path: pathlib.Path) -> None:
    p = tmp_path / "float.json"
    p.write_text('{"schema_version":"EX-K3-C5-CERT-1.0","x":1.5}', encoding="utf-8")
    with pytest.raises(VerificationError, match="floating-point"):
        verify_file(p)


def test_reject_nan_constant_in_json(tmp_path: pathlib.Path) -> None:
    p = tmp_path / "nan.json"
    p.write_text('{"schema_version":"EX-K3-C5-CERT-1.0","x":NaN}', encoding="utf-8")
    with pytest.raises(VerificationError, match="non-finite"):
        verify_file(p)


def test_reject_duplicate_json_key(tmp_path: pathlib.Path) -> None:
    p = tmp_path / "dup.json"
    p.write_text('{"schema_version":"EX-K3-C5-CERT-1.0","schema_version":"EX-K3-C5-CERT-1.0"}', encoding="utf-8")
    with pytest.raises(VerificationError, match="Duplicate JSON key"):
        verify_file(p)


def test_reject_oversized_file(tmp_path: pathlib.Path) -> None:
    p = tmp_path / "big.json"
    p.write_bytes(b" " * (MAX_JSON_BYTES + 10))
    with pytest.raises(VerificationError, match="MAX_JSON_BYTES"):
        verify_file(p)


def test_reject_missing_or_directory_path(tmp_path: pathlib.Path) -> None:
    with pytest.raises(VerificationError, match="not a readable file"):
        verify_file(tmp_path)
    with pytest.raises(VerificationError, match="not a readable file"):
        verify_file(tmp_path / "does_not_exist.json")


def test_reject_deep_nesting_recursion_error(tmp_path: pathlib.Path) -> None:
    p = tmp_path / "deep.json"
    p.write_text("[" * 5000 + "]" * 5000, encoding="utf-8")
    with pytest.raises(VerificationError, match="Invalid JSON"):
        verify_file(p)


def test_reject_unreduced_rational() -> None:
    c = _load("C03_extremal_bip_capacity_n3.json")
    c["payload"]["weight_matrix_k"][0][2] = [142, 82]
    with pytest.raises(VerificationError, match="lowest terms"):
        verify_certificate(c)


def test_reject_boolean_as_int() -> None:
    c = _load("C01_book_k4_blocks_n10.json")
    c["payload"]["num_vertices"] = True
    with pytest.raises(VerificationError, match="Expected integer"):
        verify_certificate(c)


# ---------------------------------------------------------------------------
# 4. Mode 1 Adversarial Forgeries (Book Reduction & Capacity Bounds)
# ---------------------------------------------------------------------------

def test_mode1a_rejects_c5_graph() -> None:
    c = _load("C01_book_k4_blocks_n10.json")
    # Add edge (5, 9) creating a 5-cycle 3-5-9-8-4-3
    c["payload"]["edges"].append([5, 9])
    with pytest.raises(VerificationError, match="C_5"):
        verify_certificate(c)


def test_mode1a_rejects_edge_not_in_triangle() -> None:
    c = _load("C01_book_k4_blocks_n10.json")
    # Attach pendant vertex 10 via edge (0, 10): C_5-free, but edge (0, 10) lies in no triangle!
    c["payload"]["num_vertices"] = 11
    c["payload"]["edges"].append([0, 10])
    with pytest.raises(VerificationError, match="lies in no triangle"):
        verify_certificate(c)


def test_mode1a_rejects_self_loop_and_duplicate_edge() -> None:
    c1 = _load("C01_book_k4_blocks_n10.json")
    c1["payload"]["edges"].append([0, 0])
    with pytest.raises(VerificationError, match="Self-loop"):
        verify_certificate(c1)

    c2 = _load("C01_book_k4_blocks_n10.json")
    c2["payload"]["edges"].append([1, 0])
    with pytest.raises(VerificationError, match="Duplicate edge"):
        verify_certificate(c2)


def test_mode1a_rejects_pure_k4_with_no_books() -> None:
    c = _load("C01_book_k4_blocks_n10.json")
    c["payload"]["num_vertices"] = 4
    c["payload"]["edges"] = [[0, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 3]]
    with pytest.raises(VerificationError, match="No book blocks"):
        verify_certificate(c)


def test_mode1a_rejects_k5_minus_edge_containing_c5() -> None:
    c = _load("C01_book_k4_blocks_n10.json")
    c["payload"]["num_vertices"] = 5
    c["payload"]["edges"] = [
        [0, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 3],
        [4, 1], [4, 2], [4, 3],
    ]
    with pytest.raises(VerificationError, match="C_5"):
        verify_certificate(c)


def test_mode1b_rejects_capacity_exceeding_one() -> None:
    c = _load("C03_extremal_bip_capacity_n3.json")
    # 97/56 > sqrt(3), so C_k = 9409/9408 > 1!
    c["payload"]["weight_matrix_k"][0][2] = [97, 56]
    c["payload"]["weight_matrix_k"][1][2] = [97, 56]
    with pytest.raises(VerificationError, match="Capacity bound violated"):
        verify_certificate(c)


def test_mode1b_rejects_negative_weight() -> None:
    c = _load("C03_extremal_bip_capacity_n3.json")
    c["payload"]["weight_matrix_k"][0][2] = [-1, 2]
    with pytest.raises(VerificationError, match="Negative weight"):
        verify_certificate(c)


def test_mode1b_rejects_all_zero_matrix() -> None:
    c = _load("C03_extremal_bip_capacity_n3.json")
    c["payload"]["weight_matrix_k"] = [[[0, 1]] * 3 for _ in range(3)]
    with pytest.raises(VerificationError, match="all-zero"):
        verify_certificate(c)


# ---------------------------------------------------------------------------
# 5. Mode 2 Adversarial Forgeries (Table 1 SOS, Eq. (8), Claim 4.2 & 4.3)
# ---------------------------------------------------------------------------

def test_mode2a_rejects_non_bipartite_weight() -> None:
    c = _load("C05_table1_balanced_d1_2_n4.json")
    c["payload"]["weight_matrix_k"][0][1] = [1, 10]
    with pytest.raises(VerificationError, match="Non-bipartite"):
        verify_certificate(c)


def test_mode2a_rejects_duplicate_in_part_X() -> None:
    c = _load("C05_table1_balanced_d1_2_n4.json")
    c["payload"]["part_X"] = [0, 0]
    with pytest.raises(VerificationError, match="Duplicate vertex in part_X"):
        verify_certificate(c)


def test_mode2a_rejects_p_less_than_q() -> None:
    c = _load("C08_claim43_heterogeneous_d2_7_n7.json")
    c["payload"]["part_X"] = [0, 1, 2]
    with pytest.raises(VerificationError, match="p = |X|/n >= q"):
        verify_certificate(c)


def test_mode2a_rejects_p_ge_two_thirds() -> None:
    # n=3, X={0,1} => p=2/3 => d=0 outside (0, 1/2]!
    c = _load("C05_table1_balanced_d1_2_n4.json")
    c["payload"]["num_vertices"] = 3
    c["payload"]["part_X"] = [0, 1]
    c["payload"]["weight_matrix_k"] = [
        [[0, 1], [0, 1], [1, 1]],
        [[0, 1], [0, 1], [1, 1]],
        [[0, 1], [0, 1], [0, 1]],
    ]
    with pytest.raises(VerificationError, match="0 < d = 2 - 3p <= 1/2"):
        verify_certificate(c)


def test_mode2b_rejects_capacity_violation() -> None:
    c = _load("C07_claim43_near_extremal_d1_8_n8.json")
    c["payload"]["weight_matrix_k"][0][5] = [5, 1]
    with pytest.raises(VerificationError, match="Capacity bound violated"):
        verify_certificate(c)


def test_mode2b_exact_c07_numbers() -> None:
    res = verify_file(CERTS_DIR / "C07_claim43_near_extremal_d1_8_n8.json")
    assert res["param_d"] == [1, 8]
    # 27*t^2 must be strictly <= 4
    num, den = res["t_sq_times_27"]
    assert num <= 4 * den


# ---------------------------------------------------------------------------
# 6. Mode 3 Adversarial Forgeries (5-Walk-Free Extraction & rho Monotonicity)
# ---------------------------------------------------------------------------

def test_mode3a_rejects_triangle_creating_closed_5_walk() -> None:
    # In C10 (which has capacity slack), adding edge (0,1) inside X creates triangle 0-1-5-0 and closed 5-walk!
    c = _load("C10_five_walk_free_with_residual_n10.json")
    c["payload"]["weight_matrix_k"][0][1] = [1, 20]
    with pytest.raises(VerificationError, match="closed 5-walk"):
        verify_certificate(c)


def test_mode3a_rejects_self_loop() -> None:
    c = _load("C10_five_walk_free_with_residual_n10.json")
    c["payload"]["weight_matrix_k"][8][8] = [1, 20]
    with pytest.raises(VerificationError, match="self-loop"):
        verify_certificate(c)


def test_mode3a_rejects_non_edge_as_heavy_edge() -> None:
    c = _load("C09_five_walk_free_near_tight_n6.json")
    c["payload"]["heavy_edge_u"] = 0
    c["payload"]["heavy_edge_v"] = 1
    with pytest.raises(VerificationError, match="not an edge"):
        verify_certificate(c)


def test_mode3a_rejects_light_edge_as_heavy_edge() -> None:
    # In C10, edge (8,9) has d(8)+d(9) = 2 < 2*w*n = 32/5!
    c = _load("C10_five_walk_free_with_residual_n10.json")
    c["payload"]["heavy_edge_u"] = 8
    c["payload"]["heavy_edge_v"] = 9
    with pytest.raises(VerificationError, match="Heavy edge fails"):
        verify_certificate(c)


def test_mode3a_rejects_5_cycle() -> None:
    k5 = [[[0, 1]] * 5 for _ in range(5)]
    for i in range(5):
        k5[i][(i + 1) % 5] = [1, 2]
    c = copy.deepcopy(_load("C09_five_walk_free_near_tight_n6.json"))
    c["payload"]["num_vertices"] = 5
    c["payload"]["weight_matrix_k"] = k5
    c["payload"]["heavy_edge_u"] = 0
    c["payload"]["heavy_edge_v"] = 1
    with pytest.raises(VerificationError, match="closed 5-walk"):
        verify_certificate(c)


def test_mode3b_rejects_rho_above_one_ninth() -> None:
    c = _load("C11_rho_grid_interior.json")
    c["payload"]["rho_values"].append([1, 8])
    with pytest.raises(VerificationError, match="outside Sec. 5 range"):
        verify_certificate(c)


def test_mode3b_rejects_zero_rho() -> None:
    c = _load("C11_rho_grid_interior.json")
    c["payload"]["rho_values"][0] = [0, 1]
    with pytest.raises(VerificationError, match="outside Sec. 5 range"):
        verify_certificate(c)


def test_mode3b_rejects_duplicate_rho() -> None:
    c = _load("C11_rho_grid_interior.json")
    c["payload"]["rho_values"][1] = c["payload"]["rho_values"][0]
    with pytest.raises(VerificationError, match="Duplicate rho"):
        verify_certificate(c)


# ---------------------------------------------------------------------------
# 7. Mode 4 Adversarial Forgeries (Bollobas-Gyori Construction & Berge 3-Graphs)
# ---------------------------------------------------------------------------

def test_mode4a_rejects_c4_in_bipartite_base() -> None:
    c = _load("C13_bollobas_gyori_fano_pg22.json")
    # Add extra edge creating a C_4 between left vertices 0 and 1
    # Find a right vertex adjacent to 0 but not 1
    e_set = {(a, b) for a, b in c["payload"]["bip_edges"]}
    r_for_0 = {b for a, b in e_set if a == 0}
    r_for_1 = {b for a, b in e_set if a == 1}
    extra_r = min(r_for_0 - r_for_1)
    c["payload"]["bip_edges"].append([1, extra_r])
    with pytest.raises(VerificationError, match="C_4"):
        verify_certificate(c)


def test_mode4a_rejects_duplicate_bip_edge() -> None:
    c = _load("C13_bollobas_gyori_fano_pg22.json")
    c["payload"]["bip_edges"].append(c["payload"]["bip_edges"][0])
    with pytest.raises(VerificationError, match="Duplicate bipartite edge"):
        verify_certificate(c)


def test_mode4a_exact_fano_and_pg23_counts() -> None:
    r13 = verify_file(CERTS_DIR / "C13_bollobas_gyori_fano_pg22.json")
    assert r13["num_vertices_G"] == 21
    assert r13["triangles_G"] == 21
    assert r13["edges_G"] == 49
    r14 = verify_file(CERTS_DIR / "C14_bollobas_gyori_pg23.json")
    assert r14["num_vertices_G"] == 39
    assert r14["triangles_G"] == 52
    assert r14["edges_G"] == 117


def test_mode4b_rejects_berge_c3() -> None:
    # 3 hyperedges forming a Berge 3-cycle: {0,1,3}, {1,2,4}, {2,0,5}
    c = copy.deepcopy(_load("C16_berge_3graph_linear_girth6.json"))
    c["payload"]["num_vertices"] = 6
    c["payload"]["hyperedges"] = [[0, 1, 3], [1, 2, 4], [2, 0, 5]]
    with pytest.raises(VerificationError, match="BC_3"):
        verify_certificate(c)


def test_mode4b_rejects_berge_c4() -> None:
    c = copy.deepcopy(_load("C16_berge_3graph_linear_girth6.json"))
    c["payload"]["num_vertices"] = 8
    c["payload"]["hyperedges"] = [[0, 1, 4], [1, 2, 5], [2, 3, 6], [3, 0, 7]]
    with pytest.raises(VerificationError, match="BC_4"):
        verify_certificate(c)


def test_mode4b_rejects_berge_c5() -> None:
    c = copy.deepcopy(_load("C16_berge_3graph_linear_girth6.json"))
    c["payload"]["num_vertices"] = 10
    c["payload"]["hyperedges"] = [[0, 1, 5], [1, 2, 6], [2, 3, 7], [3, 4, 8], [4, 0, 9]]
    with pytest.raises(VerificationError, match="BC_5"):
        verify_certificate(c)


def test_mode4b_rejects_duplicate_and_degenerate_hyperedge() -> None:
    c1 = _load("C15_berge_3graph_fano_doubled.json")
    c1["payload"]["hyperedges"].append(c1["payload"]["hyperedges"][0])
    with pytest.raises(VerificationError, match="Duplicate hyperedge"):
        verify_certificate(c1)

    c2 = _load("C15_berge_3graph_fano_doubled.json")
    c2["payload"]["hyperedges"][0] = [0, 0, 1]
    with pytest.raises(VerificationError, match="3 distinct vertices"):
        verify_certificate(c2)
