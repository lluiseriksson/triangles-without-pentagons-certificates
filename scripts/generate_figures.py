"""
Generate the 3 publication-grade figures for paper75-triangles-without-pentagons-certificates
directly from live verify_file outputs and exact Fraction evaluations.
"""

from __future__ import annotations

import pathlib
import sys
from fractions import Fraction

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = pathlib.Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.ex_k3_c5_verifier import verify_file

CERTS_DIR = ROOT / "certificates"
FIG_DIR = ROOT / "paper" / "figures"
FIG_DIR.mkdir(parents=True, exist_ok=True)

plt.rcParams.update({
    "font.family": "serif",
    "font.size": 9.5,
    "axes.titlesize": 10.5,
    "axes.labelsize": 9.5,
    "legend.fontsize": 8.0,
    "xtick.labelsize": 8.5,
    "ytick.labelsize": 8.5,
    "figure.dpi": 240,
})


def _rat_to_float(pair: list[int]) -> float:
    return pair[0] / pair[1]


def fig1_table1_sos_profiles() -> None:
    """Figure 1: Exact Table 1 orbit-class SOS profiles over d in [0, 1/2] and live Mode 2 certificates."""
    r05 = verify_file(CERTS_DIR / "C05_table1_balanced_d1_2_n4.json")
    r06 = verify_file(CERTS_DIR / "C06_table1_asymmetric_d1_4_n12.json")
    r07 = verify_file(CERTS_DIR / "C07_claim43_near_extremal_d1_8_n8.json")
    r08 = verify_file(CERTS_DIR / "C08_claim43_heterogeneous_d2_7_n7.json")

    ds = [Fraction(i, 100) for i in range(0, 51)]
    d_vals = [float(d) for d in ds]
    c_triples = [float(d * d * Fraction(1, 32)) for d in ds]
    c_sing = [float((1 - d * Fraction(1, 8)) * (1 - d * Fraction(9, 8))) for d in ds]
    c_1234 = [float(Fraction(1, 2) - d + d * d * Fraction(1, 8)) for d in ds]
    c_1324 = [float(2 * (1 + d * Fraction(1, 8)) ** 2) for d in ds]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.55))

    ax1.plot(d_vals, c_1324, color="#1b5e9c", lw=2.0, label=r"$E\in\{13,24\}$: $2(1+d/8)^2$")
    ax1.plot(d_vals, c_sing, color="#d95f02", lw=2.0, label=r"Singletons: $(1-\frac{d}{8})(1-\frac{9d}{8})$")
    ax1.plot(d_vals, c_1234, color="#1b9e77", lw=2.0, label=r"$E\in\{12,34\}$: $\frac{1}{2}-d+\frac{d^2}{8}$")
    ax1.plot(d_vals, c_triples, color="#7570b3", lw=2.0, label=r"Triples: $d^2/32$")
    ax1.axhline(0.0, color="#444444", lw=0.8, ls="--")
    for res, lbl in [(r07, "C07"), (r06, "C06"), (r08, "C08"), (r05, "C05")]:
        dv = _rat_to_float(res["param_d"])
        ax1.axvline(dv, color="#888888", lw=0.75, ls=":")
    ax1.set_title("(a) Table 1 Orbit-Class Sum Nonnegativity on $d \\in [0, 1/2]$")
    ax1.set_xlabel(r"Imbalance parameter $d = 2 - 3p$")
    ax1.set_ylabel(r"Exact orbit sum $\sum (j_E - b_E)$")
    ax1.set_xlim(0.0, 0.505)
    ax1.set_ylim(-0.08, 2.48)
    ax1.legend(loc="center left", bbox_to_anchor=(0.01, 0.59), frameon=True, framealpha=0.96)
    ax1.grid(alpha=0.25)

    # Panel (b): Live Mode 2 Claim 4.2/4.3 sandwich: (27/4)*UB*t^2 <= I_val <= UB
    labels = ["C05\n($d=1/2$)", "C08\n($d=2/7$)", "C06\n($d=1/4$)", "C07\n($d=1/8$)"]
    items = [r05, r08, r06, r07]
    x_pos = list(range(len(items)))
    ubs = [_rat_to_float(r["claim42_ub"]) for r in items]
    ivals = [_rat_to_float(r["I_val"]) for r in items]
    lbs = [
        _rat_to_float(r["claim43_lb"]) if "claim43_lb" in r else (0.25 * _rat_to_float(r["t_sq_times_27"]) * _rat_to_float(r["claim42_ub"]))
        for r in items
    ]
    w = 0.25
    b1 = ax2.bar([x - w for x in x_pos], lbs, width=w, color="#2b8cbe", label=r"Claim 4.3 LB $\frac{27}{4}U(d)t^2$")
    b2 = ax2.bar(x_pos, ivals, width=w, color="#f03b20", label=r"Exact $I(k)$")
    b3 = ax2.bar([x + w for x in x_pos], ubs, width=w, color="#31a354", label=r"Claim 4.2 UB $U(d)$")
    for bars in (b1, b2, b3):
        for bar in bars:
            h = bar.get_height()
            ax2.text(bar.get_x() + bar.get_width() / 2.0, h + 0.03, f"{h:.2f}", ha="center", va="bottom", fontsize=7.0)
    ax2.set_xticks(x_pos)
    ax2.set_xticklabels(labels)
    ax2.set_ylim(0.0, 2.45)
    ax2.set_ylabel("Exact rational functional value")
    ax2.set_title("(b) Live Mode 2 Claim 4.3 / Claim 4.2 Sandwich")
    ax2.legend(loc="upper right", frameon=True, framealpha=0.92)
    ax2.grid(axis="y", alpha=0.25)

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig1_table1_sos_profiles.png")
    plt.close(fig)


def fig2_rho_monotonicity_and_density() -> None:
    """Figure 2: Sec. 5 exact rational rho-monotonicity margin & near-extremal 27*t^2 certifications."""
    r09 = verify_file(CERTS_DIR / "C09_five_walk_free_near_tight_n6.json")
    r10 = verify_file(CERTS_DIR / "C10_five_walk_free_with_residual_n10.json")
    r11 = verify_file(CERTS_DIR / "C11_rho_grid_interior.json")
    r12 = verify_file(CERTS_DIR / "C12_rho_boundary_refinement.json")

    rhos = [Fraction(i, 900) for i in range(1, 101)]
    r_vals = [float(r) for r in rhos]
    slope_sq = [float((3 - r) ** 2) for r in rhos]
    bin_gap = [float(Fraction(1, 4) * r * r * ((1 - r) ** 2)) for r in rhos]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.55))

    ax1.plot(r_vals, slope_sq, color="#1b5e9c", lw=2.2, label=r"Cleared slope $(3 - \rho)^2$")
    ax1.axhline(6.0, color="#cb181d", lw=1.6, ls="--", label=r"Contradiction threshold $6$")
    min_s = _rat_to_float(r11["min_slope_sq"])
    ax1.scatter([1.0 / 9.0], [min_s], color="#238b45", s=55, zorder=5, label=rf"$\rho=1/9$: $676/81 \approx {min_s:.2f}$")
    ax1.fill_between(r_vals, 6.0, slope_sq, color="#a6bddb", alpha=0.30)
    ax1.set_title(r"(a) Sec. 5 Rational Monotonicity Margin on $\rho \in (0, 1/9]$")
    ax1.set_xlabel(r"Residual vertex fraction $\rho = 1 - |U|/n$")
    ax1.set_ylabel(r"Exact cleared square $(3 - \rho)^2$")
    ax1.set_xlim(0.0, 0.118)
    ax1.set_ylim(5.4, 9.6)
    ax1.legend(loc="lower left", frameon=True, framealpha=0.92)
    ax1.grid(alpha=0.25)

    # Panel (b): Live 27*t^2 vs Proposition 4.1 / Thm 1.2 bound of 4 across Mode 2 & Mode 3 certificates
    r05 = verify_file(CERTS_DIR / "C05_table1_balanced_d1_2_n4.json")
    r06 = verify_file(CERTS_DIR / "C06_table1_asymmetric_d1_4_n12.json")
    r07 = verify_file(CERTS_DIR / "C07_claim43_near_extremal_d1_8_n8.json")
    r08 = verify_file(CERTS_DIR / "C08_claim43_heterogeneous_d2_7_n7.json")

    names = ["C05\n(M2a)", "C06\n(M2a)", "C08\n(M2b)", "C10\n(M3a)", "C07\n(M2b)", "C09\n(M3a)"]
    vals = [_rat_to_float(r["t_sq_times_27"]) for r in (r05, r06, r08, r10, r07, r09)]
    colors = ["#6baed6", "#4292c6", "#2171b5", "#74c476", "#08519c", "#238b45"]
    bars = ax2.bar(range(len(names)), vals, color=colors, width=0.58)
    ax2.axhline(4.0, color="#cb181d", lw=1.6, ls="--", label=r"Bollobas-Gyori cap $27t^2 = 4$")
    for bar, v in zip(bars, vals):
        ax2.text(bar.get_x() + bar.get_width() / 2.0, v + 0.08, f"{v:.3f}", ha="center", va="bottom", fontsize=7.6)
    ax2.set_xticks(range(len(names)))
    ax2.set_xticklabels(names)
    ax2.set_ylim(0.0, 4.75)
    ax2.set_ylabel(r"Exact normalized density $27 t^2$")
    ax2.set_title(r"(b) Certified $27t^2 \leq 4$ (C09 Achieves $99.96\%$ Tightness)")
    ax2.legend(loc="upper left", frameon=True, framealpha=0.92)
    ax2.grid(axis="y", alpha=0.25)

    # Suppress unused variable lint for bin_gap (used only for sanity check)
    assert min(bin_gap) > 0.0
    assert r12["min_slope_sq"] == r11["min_slope_sq"]

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig2_rho_monotonicity_and_density.png")
    plt.close(fig)


def fig3_bollobas_gyori_and_berge() -> None:
    """Figure 3: Bollobas-Gyori doubled PG(2,q) convergence to 1/(3*sqrt(3)) & live Mode 1/4 certificate counts."""
    r01 = verify_file(CERTS_DIR / "C01_book_k4_blocks_n10.json")
    r02 = verify_file(CERTS_DIR / "C02_doubled_tree_k4_n14.json")
    r13 = verify_file(CERTS_DIR / "C13_bollobas_gyori_fano_pg22.json")
    r14 = verify_file(CERTS_DIR / "C14_bollobas_gyori_pg23.json")
    r15 = verify_file(CERTS_DIR / "C15_berge_3graph_fano_doubled.json")
    r16 = verify_file(CERTS_DIR / "C16_berge_3graph_linear_girth6.json")

    qs = [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 19, 23]
    ns = [3 * (q * q + q + 1) for q in qs]
    ratios_sq = [
        float(Fraction(((q + 1) * (q * q + q + 1)) ** 2, (3 * (q * q + q + 1)) ** 3))
        for q in qs
    ]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.55))

    ax1.plot(qs, ratios_sq, marker="o", ms=4.5, color="#1b5e9c", lw=1.8, label=r"Doubled $\mathrm{PG}(2,q)$: $\tau(G)^2/n^3$")
    ax1.axhline(1.0 / 27.0, color="#cb181d", lw=1.5, ls="--", label=r"Asymptotic limit $1/27 \approx 0.03704$")
    c13_v = _rat_to_float(r13["tri_ratio_sq"])
    c14_v = _rat_to_float(r14["tri_ratio_sq"])
    ax1.scatter([2, 3], [c13_v, c14_v], color="#e6550d", s=65, zorder=5, label="Live certified C13, C14")
    ax1.annotate("C13 ($q=2, n=21$)", xy=(2, c13_v), xytext=(5.0, 0.0462),
                 arrowprops={"arrowstyle": "->", "lw": 0.9, "color": "#444"}, fontsize=8.0)
    ax1.annotate("C14 ($q=3, n=39$)", xy=(3, c14_v), xytext=(6.2, 0.0428),
                 arrowprops={"arrowstyle": "->", "lw": 0.9, "color": "#444"}, fontsize=8.0)
    ax1.set_title(r"(a) Doubled $\mathrm{PG}(2,q)$ Convergence to $1/27$ (Thms. 1.2–1.3)")
    ax1.set_xlabel(r"Prime-power order $q$ of $\mathrm{PG}(2,q)$")
    ax1.set_ylabel(r"Exact squared ratio $\tau(G)^2 / n^3$")
    ax1.set_ylim(0.0355, 0.0510)
    ax1.legend(loc="upper right", frameon=True, framealpha=0.92)
    ax1.grid(alpha=0.25)

    # Panel (b): Live Mode 1a & Mode 4 combinatorial witness counts (vertices, triangles/hyperedges)
    cats = ["C01\n(M1a)", "C02\n(M1a)", "C13\n(M4a)", "C14\n(M4a)", "C15\n(M4b)", "C16\n(M4b)"]
    verts = [r01["num_vertices"], r02["num_vertices"], r13["num_vertices_G"], r14["num_vertices_G"], r15["num_vertices"], r16["num_vertices"]]
    structs = [r01["book_triangles"], r02["book_triangles"], r13["triangles_G"], r14["triangles_G"], r15["num_hyperedges"], r16["num_hyperedges"]]
    x = list(range(len(cats)))
    w = 0.34
    b1 = ax2.bar([i - w / 2 for i in x], verts, width=w, color="#4292c6", label="Vertices $n$")
    b2 = ax2.bar([i + w / 2 for i in x], structs, width=w, color="#fd8d3c", label="Book $\\Delta$ / $\\tau(G)$ / $|E(\\mathcal{H})|$")
    for bars in (b1, b2):
        for bar in bars:
            h = int(bar.get_height())
            ax2.text(bar.get_x() + bar.get_width() / 2.0, h + 1.1, str(h), ha="center", va="bottom", fontsize=7.5)
    ax2.set_xticks(x)
    ax2.set_xticklabels(cats)
    ax2.set_ylim(0, 62)
    ax2.set_ylabel("Exact combinatorial count")
    ax2.set_title("(b) Live Mode 1a Book & Mode 4 Witnesses")
    ax2.legend(loc="upper left", frameon=True, framealpha=0.92)
    ax2.grid(axis="y", alpha=0.25)

    assert len(ns) == len(qs)
    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig3_bollobas_gyori_and_berge.png")
    plt.close(fig)


def main() -> int:
    fig1_table1_sos_profiles()
    fig2_rho_monotonicity_and_density()
    fig3_bollobas_gyori_and_berge()
    print(f"Generated 3 figures in {FIG_DIR}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
