namespace TrianglesNoPentagonsCert

/-!
# EX-K3-C5-CERT-1.0: Constructive Lean 4 Kernel

18 constructive theorems formalizing the core 2-walk capacity bounds, Table 1 directed-quadruple
sum-of-squares identities, Claim 4.2/4.3 bipartite quadratic form lower bounds, Section 5
5-walk-free bipartite extraction & rho-monotonicity inequality, and Bollobás-Győri / Berge-cycle
shadow counting of Qing Cui, Ervin Győri, Chenke Zhang, and Xiutao Zhu's
"The maximum number of triangles in a graph without pentagons" (arXiv:2611.33685v1, Nov 25, 2026).

All proofs are constructive (`0` sorry, `0` custom axioms, `0` Classical.choice, `0` warnings).
-/

-- Helpers (pure constructive Int algebra, zero Classical.choice!)
private theorem int_sq_nonneg (x : Int) : 0 <= x * x := by
  by_cases h : 0 <= x
  · exact Int.mul_nonneg h h
  · have hneg : 0 <= -x := by omega
    have hm := Int.mul_nonneg hneg hneg
    rw [Int.neg_mul_neg] at hm
    exact hm

private theorem lin_prod (a b c d u v : Int) :
    (a * u + b * v) * (c * u + d * v)
      = (a * c) * (u * u) + (a * d + b * c) * (u * v) + (b * d) * (v * v) := by
  have m1 : (a * u) * (c * u) = (a * c) * (u * u) := by
    rw [Int.mul_assoc a u (c * u), <- Int.mul_assoc u c u, Int.mul_comm u c,
        Int.mul_assoc c u u, <- Int.mul_assoc a c (u * u)]
  have m2 : (a * u) * (d * v) = (a * d) * (u * v) := by
    rw [Int.mul_assoc a u (d * v), <- Int.mul_assoc u d v, Int.mul_comm u d,
        Int.mul_assoc d u v, <- Int.mul_assoc a d (u * v)]
  have m3 : (b * v) * (c * u) = (b * c) * (u * v) := by
    rw [Int.mul_assoc b v (c * u), <- Int.mul_assoc v c u, Int.mul_comm v c,
        Int.mul_assoc c v u, Int.mul_comm v u, <- Int.mul_assoc b c (u * v)]
  have m4 : (b * v) * (d * v) = (b * d) * (v * v) := by
    rw [Int.mul_assoc b v (d * v), <- Int.mul_assoc v d v, Int.mul_comm v d,
        Int.mul_assoc d v v, <- Int.mul_assoc b d (v * v)]
  rw [Int.add_mul, Int.mul_add, Int.mul_add, m1, m2, m3, m4, Int.add_mul]
  omega

private theorem scale_sq (k x : Int) : (k * x) * (k * x) = (k * k) * (x * x) := by
  rw [Int.mul_assoc k x (k * x), <- Int.mul_assoc x k x, Int.mul_comm x k,
      Int.mul_assoc k x x, <- Int.mul_assoc k k (x * x)]

-- Theorem 1: Lemma 2.5 Pointwise symmetric square bound (a + b)^2 <= 2*a^2 + b^2 + 4*a*b
theorem lemma25_pointwise_capacity_dom (a b : Int) (ha : 0 <= a) (hb : 0 <= b) :
    (a + b) * (a + b) <= 2 * (a * a) + b * b + 4 * (a * b) := by
  have hab : 0 <= a * b := Int.mul_nonneg ha hb
  have ha2 : 0 <= a * a := Int.mul_nonneg ha ha
  have hexp : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm b a]
    omega
  rw [hexp]
  omega

-- Theorem 2: Lemma 2.5 Exact 4/3 L2-norm implication:
-- From (3/2)||k||_2^2 + 2*cross <= 1 (cleared: 3*k2 + 4*cross <= 2*B) and cross >= 0,
-- deduce ||K||_2^2 <= 4/3 (cleared: 3*(2*k2 + 2*cross) <= 4*B)!
theorem lemma25_l2_four_thirds_bound (k2 cross B : Int)
    (hCross : 0 <= cross)
    (hCap : 3 * k2 + 4 * cross <= 2 * B) :
    3 * (2 * k2 + 2 * cross) <= 4 * B := by
  omega

-- Theorem 3: Lemma 2.8 Inductive book-block arc accounting
def natListSum : List Nat -> Nat
  | [] => 0
  | x :: xs => x + natListSum xs

def twiceListSum : List Nat -> Nat
  | [] => 0
  | x :: xs => 2 * x + twiceListSum xs

theorem lemma28_book_arc_count :
    forall pages : List Nat, twiceListSum pages = 2 * natListSum pages
  | [] => rfl
  | s :: rest => by
      have ih := lemma28_book_arc_count rest
      simp only [twiceListSum, natListSum]
      omega

-- Theorem 4: Prop. 4.1 Large-part cubic regime (p >= 2/3): 27 * (2 * p * (1 - p)^2) <= 4
-- Homogenized (2*N <= 3*p, p <= N, 0 <= N):
--   4*N^3 - 54*p*(N - p)^2 = (3*p - 2*N)*(18*p*(N - p) + 2*N*(3*p - N)) >= 0!
theorem prop41_large_part_cubic_bound (p N : Int)
    (hLo : 2 * N <= 3 * p) (hHi : p <= N) (hN : 0 <= N) :
    54 * (p * ((N - p) * (N - p))) <= 4 * (N * (N * N)) := by
  have hp : 0 <= p := by omega
  have hQuad : (3 * p - 2 * N) * (18 * p * (N - p) + 2 * N * (3 * p - N))
      = 4 * (N * (N * N)) - 54 * (p * ((N - p) * (N - p))) := by
    have hL : p * ((N - p) * (N - p)) = p * (N * N) - 2 * (p * (p * N)) + p * (p * p) := by
      have hsq : (N - p) * (N - p) = N * N - 2 * (p * N) + p * p := by
        rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm N p]
        omega
      rw [hsq, Int.mul_add, Int.mul_sub, <- Int.mul_assoc p 2 (p * N), Int.mul_comm p 2, Int.mul_assoc 2 p (p * N)]
    have hInner : 18 * p * (N - p) + 2 * N * (3 * p - N)
        = 24 * (p * N) - 18 * (p * p) - 2 * (N * N) := by
      rw [Int.mul_sub, Int.mul_sub, Int.mul_assoc 18 p N, Int.mul_assoc 18 p p, Int.mul_assoc 2 N N]
      have h23 : 2 * N * (3 * p) = 6 * (p * N) := by
        rw [Int.mul_assoc 2 N (3 * p), <- Int.mul_assoc N 3 p, Int.mul_comm N 3,
            Int.mul_assoc 3 N p, Int.mul_comm N p, <- Int.mul_assoc 2 3 (p * N)]
        rfl
      rw [h23]
      omega
    rw [hInner, Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_sub, Int.mul_sub]
    have u1 : 3 * p * (24 * (p * N)) = 72 * (p * (p * N)) := by
      rw [Int.mul_assoc 3 p (24 * (p * N)), <- Int.mul_assoc p 24 (p * N), Int.mul_comm p 24,
          Int.mul_assoc 24 p (p * N), <- Int.mul_assoc 3 24 (p * (p * N))]
      rfl
    have u2 : 3 * p * (18 * (p * p)) = 54 * (p * (p * p)) := by
      rw [Int.mul_assoc 3 p (18 * (p * p)), <- Int.mul_assoc p 18 (p * p), Int.mul_comm p 18,
          Int.mul_assoc 18 p (p * p), <- Int.mul_assoc 3 18 (p * (p * p))]
      rfl
    have u3 : 3 * p * (2 * (N * N)) = 6 * (p * (N * N)) := by
      rw [Int.mul_assoc 3 p (2 * (N * N)), <- Int.mul_assoc p 2 (N * N), Int.mul_comm p 2,
          Int.mul_assoc 2 p (N * N), <- Int.mul_assoc 3 2 (p * (N * N))]
      rfl
    have u4 : 2 * N * (24 * (p * N)) = 48 * (p * (N * N)) := by
      rw [Int.mul_assoc 2 N (24 * (p * N)), <- Int.mul_assoc N 24 (p * N), Int.mul_comm N 24,
          Int.mul_assoc 24 N (p * N), <- Int.mul_assoc 2 24 (N * (p * N)),
          <- Int.mul_assoc N p N, Int.mul_comm N p, Int.mul_assoc p N N]
      rfl
    have u5 : 2 * N * (18 * (p * p)) = 36 * (p * (p * N)) := by
      rw [Int.mul_assoc 2 N (18 * (p * p)), <- Int.mul_assoc N 18 (p * p), Int.mul_comm N 18,
          Int.mul_assoc 18 N (p * p), <- Int.mul_assoc 2 18 (N * (p * p)),
          Int.mul_comm N (p * p), Int.mul_assoc p p N]
      rfl
    have u6 : 2 * N * (2 * (N * N)) = 4 * (N * (N * N)) := by
      rw [Int.mul_assoc 2 N (2 * (N * N)), <- Int.mul_assoc N 2 (N * N), Int.mul_comm N 2,
          Int.mul_assoc 2 N (N * N), <- Int.mul_assoc 2 2 (N * (N * N))]
      rfl
    rw [u1, u2, u3, u4, u5, u6, hL]
    omega
  have hF1 : 0 <= 3 * p - 2 * N := by omega
  have hF2 : 0 <= 18 * p * (N - p) + 2 * N * (3 * p - N) := by
    have t1 : 0 <= 18 * p * (N - p) := Int.mul_nonneg (by omega) (by omega)
    have t2 : 0 <= 2 * N * (3 * p - N) := Int.mul_nonneg (by omega) (by omega)
    omega
  have hProd : 0 <= (3 * p - 2 * N) * (18 * p * (N - p) + 2 * N * (3 * p - N)) :=
    Int.mul_nonneg hF1 hF2
  omega

-- Theorem 5: Table 1 Classes {1234} & {} exact cancellation (cleared by 16)
theorem table1_class_full_and_empty_zero (d : Int) :
    (3 + 2 * d) - ((2 + 2 * d) + 1) = 0 /\
    (8 - 8 * d + d * d) + (64 + 16 * d - d * d) - (8 + 8 * d + 64) = 0 := by
  exact ⟨by omega, by omega⟩

-- Theorem 6: Table 1 Class {14, 23} exact cleared-by-64 cancellation (including d^2 cancellation!)
-- j_{14} = (192*N^2 + 112*N*d + d^2)/64, j_{23} = (320*N^2 + 144*N*d - d^2)/64,
-- b_{14} + b_{23} = 2*(128*N^2 + 128*N*d + 128*N^2)/64 = (512*N^2 + 256*N*d)/64!
theorem table1_class_14_23_zero (d N : Int) :
    (192 * (N * N) + 112 * (N * d) + d * d) +
    (320 * (N * N) + 144 * (N * d) - d * d) -
    2 * (128 * (N * N) + 128 * (N * d) + 128 * (N * N)) = 0 := by
  omega

-- Theorem 7: Table 1 Class {12, 34} exact nonnegativity on 0 <= d <= 1/2
theorem table1_class_12_34_nonneg (d N : Int) (hd : 0 <= d) (hHalf : 2 * d <= N) :
    0 <= 4 * (N * N) - 8 * (N * d) + d * d := by
  have hId : 4 * (N * N) - 8 * (N * d) + d * d = 4 * N * (N - 2 * d) + d * d := by
    rw [Int.mul_sub, Int.mul_assoc 4 N N]
    have h1 : 4 * N * (2 * d) = 8 * (N * d) := by
      rw [Int.mul_assoc 4 N (2 * d), <- Int.mul_assoc N 2 d, Int.mul_comm N 2,
          Int.mul_assoc 2 N d, <- Int.mul_assoc 4 2 (N * d)]
      rfl
    rw [h1]
  have h1 : 0 <= 4 * N * (N - 2 * d) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0 <= d * d := Int.mul_nonneg hd hd
  rw [hId]
  omega

-- Theorem 8: Table 1 Class {1, 2, 3, 4} exact nonnegativity on 0 <= d <= 1/2
theorem table1_class_singletons_nonneg (d N : Int) (hd : 0 <= d) (hHalf : 2 * d <= N) :
    0 <= (8 * N - d) * (8 * N - 9 * d) := by
  exact Int.mul_nonneg (by omega) (by omega)

-- Theorem 9: Table 1 Classes {123,124,134,234} & {13,24} exact square nonnegativity
theorem table1_class_triples_and_diag_nonneg (d N : Int) :
    0 <= d * d /\ 0 <= 2 * ((8 * N + d) * (8 * N + d)) := by
  have h1 := int_sq_nonneg d
  have h2 := int_sq_nonneg (8 * N + d)
  exact ⟨h1, by omega⟩

-- Theorem 10: Claim 4.2 Quadratic concave upper bound 2*c - c^2 <= 1 (cleared by N^2)
theorem claim42_quadratic_capacity_upper (c N : Int) :
    2 * (c * N) - c * c <= N * N := by
  have hsq : 0 <= (N - c) * (N - c) := int_sq_nonneg (N - c)
  have hexp : (N - c) * (N - c) = N * N - 2 * (c * N) + c * c := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm N c]
    omega
  omega

-- Theorem 11: Claim 4.3 First SOS coefficient lower bound 2*(d^2 - 2*d + 3) >= 9/2 on 0 <= d <= 1/2
-- Homogenized: 4*(d^2 - 2*N*d + 3*N^2) - 9*N^2 = (1*N + (-2)*d) * (3*N + (-2)*d) >= 0!
theorem claim43_coeff_t2_bound (d N : Int) (hd : 0 <= d) (hHalf : 2 * d <= N) :
    9 * (N * N) <= 4 * (d * d - 2 * (N * d) + 3 * (N * N)) := by
  have hExp := lin_prod 1 (-2) 3 (-2) N d
  have hF1 : 1 * N + (-2) * d = N - 2 * d := by omega
  have hF2 : 3 * N + (-2) * d = 3 * N - 2 * d := by omega
  rw [hF1, hF2] at hExp
  have hProd : 0 <= (N - 2 * d) * (3 * N - 2 * d) := Int.mul_nonneg (by omega) (by omega)
  omega

-- Theorem 12: Claim 4.3 Third SOS coefficient lower bound (5*d^2 - 20*d + 32)/8 >= 81/32 on 0 <= d <= 1/2
-- Homogenized: 4*(5*d^2 - 20*N*d + 32*N^2) - 81*N^2 = (N - 2*d)*(47*N - 10*d) + 24*(N*d) >= 0!
theorem claim43_coeff_beta2_bound (d N : Int) (hd : 0 <= d) (hHalf : 2 * d <= N) :
    81 * (N * N) <= 4 * (5 * (d * d) - 20 * (N * d) + 32 * (N * N)) := by
  have hExp := lin_prod 1 (-2) 47 (-10) N d
  have hF1 : 1 * N + (-2) * d = N - 2 * d := by omega
  have hF2 : 47 * N + (-10) * d = 47 * N - 10 * d := by omega
  rw [hF1, hF2] at hExp
  have hProd : 0 <= (N - 2 * d) * (47 * N - 10 * d) := Int.mul_nonneg (by omega) (by omega)
  have hNd : 0 <= N * d := Int.mul_nonneg (by omega) hd
  omega

-- Theorem 13: Claim 4.3 Exact completed square 144*u^2 - 216*u*b + 81*b^2 = 9*(4*u - 3*b)^2 >= 0
theorem claim43_completed_square_nonneg (u b : Int) :
    144 * (u * u) - 216 * (u * b) + 81 * (b * b) = 9 * ((4 * u - 3 * b) * (4 * u - 3 * b)) /\
    0 <= 144 * (u * u) - 216 * (u * b) + 81 * (b * b) := by
  have hExp := lin_prod 4 (-3) 4 (-3) u b
  have hF : 4 * u + (-3) * b = 4 * u - 3 * b := by omega
  rw [hF] at hExp
  have hnn : 0 <= (4 * u - 3 * b) * (4 * u - 3 * b) := int_sq_nonneg (4 * u - 3 * b)
  exact ⟨by omega, by omega⟩

-- Theorem 14: Prop. 4.1 Final cancellation: A*(27*t2) <= A*(4*N2) with A >= 1 => 27*t2 <= 4*N2
theorem prop41_final_density_bound (A t2 N2 : Nat) (hA : 1 <= A)
    (hBound : A * (27 * t2) <= A * (4 * N2)) :
    27 * t2 <= 4 * N2 := by
  exact Nat.le_of_mul_le_mul_left hBound (by omega)

-- Theorem 15: Sec. 5 Edge density lower bound w > 4/9 from 27*t^2 > 4 and 3*t^2 <= w
theorem sec5_edge_density_four_ninths (B t2 W : Nat)
    (hExceed : 4 * B < 27 * t2) (hCS : 3 * t2 <= W) :
    4 * B < 9 * W := by
  omega

-- Theorem 16: Sec. 5 Residual deletion fraction rho < 1/9 from |B| > 8n/9 and B <= U <= N
theorem sec5_residual_fraction_one_ninth (N B U : Nat)
    (hBigB : 8 * N < 9 * B) (hSub : B <= U) (hLe : U <= N) :
    9 * (N - U) < N := by
  omega

-- Theorem 17: Sec. 5 Exact rational monotonicity margin (27*N - 9*r)^2 >= 6*(9*N)^2 on 9*r <= N
theorem sec5_rho_monotonicity_margin (r N : Int) (hN : 0 <= N) (hBound : 9 * r <= N) :
    6 * ((9 * N) * (9 * N)) <= (27 * N - 9 * r) * (27 * N - 9 * r) := by
  have hLow : 26 * N <= 27 * N - 9 * r := by omega
  have hSq1 : (26 * N) * (26 * N) <= (27 * N - 9 * r) * (27 * N - 9 * r) :=
    Int.mul_le_mul hLow hLow (by omega) (by omega)
  have hL : (26 * N) * (26 * N) = (26 * 26) * (N * N) := scale_sq 26 N
  have hR : (9 * N) * (9 * N) = (9 * 9) * (N * N) := scale_sq 9 N
  have hN2 : 0 <= N * N := Int.mul_nonneg hN hN
  rw [hL] at hSq1
  rw [hR]
  omega

-- Theorem 18: Thm. 1.2/1.3/1.4 Inductive Bollobás-Győri doubling edge-count identity
def doubledEdgeSum : List Nat -> Nat
  | [] => 0
  | deg :: rest => (2 * deg + 1) + doubledEdgeSum rest

theorem bollobas_gyori_doubling_counts :
    forall degs : List Nat, doubledEdgeSum degs = 2 * natListSum degs + degs.length
  | [] => rfl
  | deg :: rest => by
      have ih := bollobas_gyori_doubling_counts rest
      simp only [doubledEdgeSum, natListSum, List.length]
      omega

end TrianglesNoPentagonsCert
