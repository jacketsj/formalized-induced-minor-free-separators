/-
# Rabinovich Embeddings: Large-Core and Well-Spread Cases

This file proves two key lemmas about non-expansive embeddings into the line
with bounded average distortion.

## Main Results

* `infDist_nonExpansive` - distance-to-set embeddings are non-expansive
* `large_core_case` - if a ball contains ≥ εn points, the distance-to-ball
  embedding has small average distortion
* `well_spread_case` - if two large sets are far apart, the distance-to-set
  embedding has small average distortion

## References

Section "Rabinovich Embeddings" of "Separators of String Graphs,
Region-Intersection Graphs, and Induced-Minor-Free Graphs, Revisited".
-/
import Mathlib
import InducedMinorFreeSeparators.ProofDefs

open Finset BigOperators Metric

/-! ## Non-expansiveness of distance-to-set embeddings -/

/-- The embedding `x ↦ infDist x S` is non-expansive. -/
theorem infDist_nonExpansive {X : Type*} [PseudoMetricSpace X] (S : Set X) :
    IsNonExpansive (fun x => Metric.infDist x S) := by
  intro x y
  rw [abs_le]
  constructor
  · linarith [Metric.infDist_le_infDist_add_dist (s := S) (x := y) (y := x), dist_comm x y]
  · linarith [Metric.infDist_le_infDist_add_dist (s := S) (x := x) (y := y)]

/-- For `x ∈ S`, `infDist x S = 0`. -/
theorem infDist_eq_zero_of_mem' {X : Type*} [PseudoMetricSpace X]
    {x : X} {S : Set X} (hx : x ∈ S) :
    Metric.infDist x S = 0 :=
  Metric.infDist_zero_of_mem hx

variable {X : Type*} [PseudoMetricSpace X] [Fintype X]

/-! ## Key summation lemmas -/

/-
For any `x₀` and `S` with `x₀ ∈ S` and `S ⊆ B(x₀, r)`, we have
`d(u, S) ≥ d(u, x₀) - r` for all `u`.
-/
omit [Fintype X] in
theorem infDist_le_dist_center_add_radius {x₀ : X} {S : Set X}
    (hx₀ : x₀ ∈ S) {r : ℝ} (hS : S ⊆ Metric.closedBall x₀ r) (u : X) :
    dist u x₀ - r ≤ Metric.infDist u S := by
  have h_le : ∀ s ∈ S, dist u x₀ - r ≤ dist u s := by
    intro s hs; have := hS hs; rw [ Metric.mem_closedBall ] at this; linarith [ dist_triangle u s x₀ ] ;
  convert le_ciInf fun s => ?_;
  rw [ Metric.infDist_eq_iInf ];
  · exact ⟨ x₀, hx₀ ⟩;
  · exact h_le _ s.2

/-
The triangle inequality gives: Σ_{u,v} d(u,v) ≤ 2n · Σ_u d(u, x₀).
-/
theorem pairDistSum_le_two_mul_sum_dist_center (x₀ : X) :
    pairDistSum X ≤ 2 * (Fintype.card X : ℝ) * ∑ u : X, dist u x₀ := by
  -- By the triangle inequality, we have $d(u, v) \leq d(u, x₀) + d(v, x₀)$ for all $u, v \in X$.
  have h_triangle : ∀ u v : X, dist u v ≤ dist u x₀ + dist v x₀ := by
    exact fun u v => dist_triangle_right _ _ _;
  convert Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun v hv => h_triangle u v using 1 ; norm_num [ Finset.sum_add_distrib ] ; ring_nf;
  rw [ ← Finset.mul_sum _ _ _ ] ; ring;

/-
Core embedding estimate: the embedding sum is bounded below by
`|S| * Σ_u infDist u S`.
-/
theorem embeddingSum_infDist_ge_card_mul_sum (S : Finset X) :
    (S.card : ℝ) * ∑ u : X, Metric.infDist u (↑S : Set X) ≤
      ∑ x : X, ∑ y : X, |Metric.infDist x ↑S - Metric.infDist y ↑S| := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ x : X, ∑ y : X, |Metric.infDist x S - Metric.infDist y S| ≥ ∑ x ∈ S, ∑ y : X, |Metric.infDist x S - Metric.infDist y S| := by
    exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_univ S ) fun _ _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _;
  -- For $x \in S$, $\infDist x S = 0$, so $|\infDist x S - \infDist y S| = \infDist y S$.
  have h_zero : ∀ x ∈ S, ∑ y : X, |Metric.infDist x S - Metric.infDist y S| = ∑ y : X, Metric.infDist y S := by
    intro x hx
    have h_zero : Metric.infDist x S = 0 := by
      exact Metric.infDist_zero_of_mem hx;
    exact Finset.sum_congr rfl fun y _ => by rw [ h_zero, zero_sub, abs_neg, abs_of_nonneg ( Metric.infDist_nonneg ) ] ;
  exact le_trans ( by rw [ Finset.sum_congr rfl h_zero, Finset.sum_const, nsmul_eq_mul ] ) h_fubini

/-! ## Large-Core Case -/

/-
**Large-Core Case** (Lemma 6.1 from the paper).

Given a finite pseudometric space `(X, d)` with `n` points, let
`Δ = (Σ d(x,y)) / n²` be the average pairwise distance.
If there exists `x₀ ∈ X` such that the ball `B(x₀, Δ/c)` contains at least
`εn` points, then the embedding `f(x) = d(x, B(x₀, Δ/c))` satisfies:
  `Σ |f(x) - f(y)| ≥ (ε/2)(1 - 2/c) · Σ d(x,y)`.

This gives average distortion at most `[ε/2 · (1 - 2/c)]⁻¹`.
-/
theorem large_core_case (ε c : ℝ) (_hε : 0 < ε) (hc : 2 < c)
    (hn : 0 < Fintype.card X)
    (S : Finset X) (x₀ : X)
    (hx₀ : x₀ ∈ S)
    (hS_ball : ∀ s ∈ S, dist x₀ s ≤ pairDistSum X / ((Fintype.card X : ℝ)^2 * c))
    (hS_size : ε * (Fintype.card X : ℝ) ≤ (S.card : ℝ)) :
    ε / 2 * (1 - 2 / c) * pairDistSum X ≤
      embeddingSum (fun x => Metric.infDist x (↑S : Set X)) := by
  -- By pairDistSum_le_two_mul_sum_dist_center, $D \leq 2n \sum_u dist u x₀$, so $\sum_u dist u x₀ \geq D/(2n)$.
  have h_sum_dist : ∑ u : X, dist u x₀ ≥ (pairDistSum X) / (2 * (Fintype.card X : ℝ)) := by
    exact div_le_iff₀' ( by positivity ) |>.2 ( pairDistSum_le_two_mul_sum_dist_center x₀ );
  -- By infDist_le_dist_center_add_radius (with S ⊆ closedBall x₀ r since hS_ball), for each u: dist u x₀ - r ≤ infDist u S. So Σ_u infDist u S ≥ Σ_u (dist u x₀ - r) = Σ_u dist u x₀ - n*r ≥ D/(2n) - n*r = D/(2n) - D/(nc) = D(1/2 - 1/c)/n = (D/n)(1/2)(1-2/c).
  have h_sum_infDist : ∑ u : X, Metric.infDist u (S : Set X) ≥ (pairDistSum X) / (2 * (Fintype.card X : ℝ)) - (Fintype.card X : ℝ) * (pairDistSum X) / ((Fintype.card X : ℝ) ^ 2 * c) := by
    have h_sum_infDist : ∀ u : X, Metric.infDist u (S : Set X) ≥ dist u x₀ - (pairDistSum X) / ((Fintype.card X : ℝ) ^ 2 * c) := by
      intro u
      apply infDist_le_dist_center_add_radius hx₀ (fun s hs => by
        exact hS_ball s hs |> fun h => by simpa [ dist_comm ] using h;) u;
    refine' le_trans _ ( Finset.sum_le_sum fun u _ => h_sum_infDist u );
    simp_all +decide [ Finset.sum_sub_distrib  ];
    exact h_sum_dist.trans ( by ring_nf; norm_num );
  -- By embeddingSum_infDist_ge_card_mul_sum, the embeddingSum ≥ |S| * Σ_u infDist u S ≥ εn * (D/n)(1/2)(1-2/c) = ε/2*(1-2/c)*D.
  have h_embeddingSum : embeddingSum (fun x => Metric.infDist x (S : Set X)) ≥ (S.card : ℝ) * ∑ u : X, Metric.infDist u (S : Set X) := by
    apply_rules [ embeddingSum_infDist_ge_card_mul_sum ];
  refine' le_trans _ h_embeddingSum;
  refine' le_trans _ ( mul_le_mul_of_nonneg_left h_sum_infDist <| Nat.cast_nonneg _ );
  convert mul_le_mul_of_nonneg_right hS_size ( show 0 ≤ pairDistSum X / ( 2 * Fintype.card X ) - Fintype.card X * pairDistSum X / ( Fintype.card X ^ 2 * c ) from sub_nonneg_of_le ?_ ) using 1 ; ring_nf;
  · simp +decide [ hn.ne' ];
  · rw [ div_le_div_iff₀ ] <;> try positivity;
    nlinarith [ show 0 ≤ pairDistSum X * ( Fintype.card X : ℝ ) ^ 2 by exact mul_nonneg ( Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg ) ( sq_nonneg _ ) ]

/-! ## Well-Spread Case -/

/-
**Well-Spread Case** (Lemma 6.2 from the paper).

Given a finite pseudometric space `(X, d)` with `n` points, let
`Δ = (Σ d(x,y)) / n²`.
If there exist sets `A, B ⊆ X` with `|A|, |B| ≥ εn` and
`d(b, A) ≥ Δ/c` for all `b ∈ B`, then the embedding `f(x) = d(x, A)` satisfies:
  `Σ |f(x) - f(y)| ≥ (ε²/c) · Σ d(x,y)`.

This gives average distortion at most `c/ε²`.
-/
theorem well_spread_case (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c)
    (hn : 0 < Fintype.card X)
    (A B : Finset X)
    (hA_size : ε * (Fintype.card X : ℝ) ≤ (A.card : ℝ))
    (hB_size : ε * (Fintype.card X : ℝ) ≤ (B.card : ℝ))
    (hAB_dist : ∀ b ∈ B,
      pairDistSum X / ((Fintype.card X : ℝ)^2 * c) ≤ Metric.infDist (b : X) (↑A : Set X)) :
    ε^2 / c * pairDistSum X ≤
      embeddingSum (fun x => Metric.infDist x (↑A : Set X)) := by
  -- Let's simplify the expression using the fact that multiplication is commutative and associative.
  suffices h_simplified : (A.card : ℝ) * (B.card : ℝ) * (pairDistSum X / (Fintype.card X ^ 2 * c)) ≤ embeddingSum (fun x => Metric.infDist x (↑A : Set X)) by
    convert h_simplified.trans' _ using 1;
    convert mul_le_mul_of_nonneg_right ( mul_le_mul hA_size hB_size ( by positivity ) ( by positivity ) ) ( show 0 ≤ pairDistSum X / ( ( Fintype.card X : ℝ ) ^ 2 * c ) by exact div_nonneg ( Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg ) ( by positivity ) ) using 1 ; ring_nf;
    simp +decide [ hn.ne' ];
  convert embeddingSum_infDist_ge_card_mul_sum A |> le_trans _ using 1;
  rw [ mul_assoc ];
  refine' mul_le_mul_of_nonneg_left _ ( Nat.cast_nonneg _ );
  refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_univ B ) fun _ _ _ => Metric.infDist_nonneg );
  convert Finset.sum_le_sum hAB_dist using 1 ; simp +decide [ mul_comm ]
