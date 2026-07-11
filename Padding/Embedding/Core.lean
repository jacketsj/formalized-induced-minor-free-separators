/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Padding.PaddedDecompDefs
import Padding.PaddedDecomp.HasPaddedModulus
import Padding.EmbeddingDefs

/-! # Proof of Non-expansive Embedding with O(log n) Average Distortion

This file contains the **proof** of `nonexpansive_avg_distortion_embedding`,
which shows that any n-point metric space admits a 1-Lipschitz embedding into ℝ
with average distortion O(log n).

For the definitions (`IsNonExpansive`, `pairDistSum`, `embeddingSum`,
`avgDistortion`), see `EmbeddingDefs.lean`.
For the padded decomposition definitions, see `PaddedDecompDefs.lean`.
For the main theorem statement, see `Embedding.lean`.

## Proof structure

- **Case I** (large cluster): When some ball contains ≥ n/10 points, the
  distance-to-ball function gives constant average distortion.
- **Case II** (no large cluster): Uses a padded decomposition with random
  cluster coloring and the signed distance function.
-/

open PaddedDecomposition MeasureTheory Metric Set Real Finset BigOperators

namespace PaddedDecomposition

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

noncomputable section

open Classical

variable {X : Type*} [MetricSpace X] [Fintype X]

/-! ## Auxiliary Lemmas -/

/-- Triangle inequality on sums: Σ d(u,v) ≤ 2n Σ d(u,x₀). -/
lemma sum_dist_le_two_mul_sum_dist_point (x₀ : X) :
    ∑ u : X, ∑ v : X, dist u v ≤
      2 * Fintype.card X * ∑ u : X, dist u x₀ := by
  have h : ∀ u v : X, dist u v ≤ dist u x₀ + dist v x₀ :=
    fun u v => dist_triangle_right _ _ _
  calc ∑ u : X, ∑ v : X, dist u v
      ≤ ∑ u : X, ∑ v : X, (dist u x₀ + dist v x₀) :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => h u v
    _ = 2 * Fintype.card X * ∑ u : X, dist u x₀ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        linarith [Finset.mul_sum Finset.univ (fun x => dist x x₀) (↑(Fintype.card X))]

/-- Distance to x₀ bounded by infDist to S plus D, when S ⊆ closedBall x₀ D. -/
lemma dist_le_infDist_add {x₀ x : X} {S : Set X} {D : ℝ}
    (hx₀ : x₀ ∈ S) (hS : S ⊆ Metric.closedBall x₀ D) :
    dist x x₀ ≤ Metric.infDist x S + D := by
  refine le_of_forall_pos_le_add fun ε εpos => ?_
  obtain ⟨z, hzS, hz⟩ := (Metric.infDist_lt_iff ⟨x₀, hx₀⟩).mp
    (show Metric.infDist x S < Metric.infDist x S + ε by linarith)
  linarith [dist_triangle x z x₀, Metric.mem_closedBall.mp (hS hzS)]

/-- Sum of |f(u) - f(v)| is large when f = 0 on a large subset S and f ≥ 0. -/
lemma sum_abs_diff_ge_of_zero_subset
    {f : X → ℝ} (hf : ∀ x, 0 ≤ f x)
    (S : Finset X) (hS : ∀ x ∈ S, f x = 0) :
    ∑ u : X, ∑ v : X, |f u - f v| ≥ S.card * ∑ u : X, f u := by
  have h : ∀ u, ∑ v ∈ S, |f u - f v| = S.card * f u := by
    intro u
    rw [Finset.sum_congr rfl (fun v hv => by rw [hS v hv, sub_zero, abs_of_nonneg (hf u)])]
    simp
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun u _ => (h u ▸
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => abs_nonneg _))

/-! ## Case I: Large Ball Exists -/

/-
**Case I**: If there exists x₀ with a ball of radius D containing ≥ n/10 points,
and 4n²D ≤ Σ dist, then infDist to the ball gives distortion ≤ 40.
-/
theorem embedding_case_one
    (x₀ : X) (D : ℝ) (hD : 0 ≤ D)
    (h_avg : 4 * (Fintype.card X : ℝ)^2 * D ≤ ∑ u : X, ∑ v : X, dist u v)
    (hlarge : Fintype.card X ≤
      10 * (Finset.univ.filter (fun x => dist x x₀ ≤ D)).card) :
    ∃ (f : X → ℝ), LipschitzWith 1 f ∧
      (∑ u : X, ∑ v : X, dist u v) ≤
        40 * (∑ u : X, ∑ v : X, |f u - f v|) := by
          refine' ⟨ fun x => Metric.infDist x ( Metric.closedBall x₀ D ), _, _ ⟩;
          · exact lipschitz_infDist_pt (closedBall x₀ D);
          · -- By sum_abs_diff_ge_of_zero_subset, we have:
            have h_sum_abs_diff : ∑ u : X, ∑ v : X, |Metric.infDist u (Metric.closedBall x₀ D) - Metric.infDist v (Metric.closedBall x₀ D)| ≥ (Finset.univ.filter (fun x => dist x x₀ ≤ D)).card * ∑ u : X, Metric.infDist u (Metric.closedBall x₀ D) := by
              apply sum_abs_diff_ge_of_zero_subset;
              · exact fun x => Metric.infDist_nonneg;
              · exact fun x hx => Metric.infDist_zero_of_mem <| by simpa using hx;
            -- By sum_dist_le_two_mul_sum_dist_point, we have:
            have h_sum_dist : ∑ u : X, ∑ v : X, dist u v ≤ 2 * (Fintype.card X : ℝ) * (∑ u : X, dist u x₀) := by
              convert sum_dist_le_two_mul_sum_dist_point x₀ using 1;
            -- By dist_le_infDist_add, we have:
            have h_dist_le_infDist_add : ∑ u : X, dist u x₀ ≤ ∑ u : X, Metric.infDist u (Metric.closedBall x₀ D) + (Fintype.card X : ℝ) * D := by
              have h_dist_le_infDist_add : ∀ u : X, dist u x₀ ≤ Metric.infDist u (Metric.closedBall x₀ D) + D := by
                exact fun u => dist_le_infDist_add ( Metric.mem_closedBall_self hD ) ( Set.Subset.refl _ );
              exact le_trans ( Finset.sum_le_sum fun _ _ => h_dist_le_infDist_add _ ) ( by simp +decide [ Finset.sum_add_distrib ] );
            nlinarith [ show ( Fintype.card X : ℝ ) ≤ 10 * Finset.card ( Finset.filter ( fun x => dist x x₀ ≤ D ) Finset.univ ) by exact_mod_cast hlarge, show ( 0 : ℝ ) ≤ ∑ u : X, Metric.infDist u ( Metric.closedBall x₀ D ) by exact Finset.sum_nonneg fun _ _ => Metric.infDist_nonneg ]

/-! ## The Signed Distance Function -/

/-- The signed distance function: `(d(x,S) - d(x,Sᶜ)) / 2`. -/
def signedDistFun (S : Set X) (x : X) : ℝ :=
  (Metric.infDist x S - Metric.infDist x Sᶜ) / 2

lemma signedDistFun_lipschitz (S : Set X) :
    LipschitzWith 1 (signedDistFun S) := by
      rw [ lipschitzWith_iff_dist_le_mul ];
      -- By definition of infimum distance, we know that
      have h_infDist_lip : ∀ x y : X, dist (Metric.infDist x S) (Metric.infDist y S) ≤ dist x y ∧ dist (Metric.infDist x Sᶜ) (Metric.infDist y Sᶜ) ≤ dist x y := by
        intro x y;
        exact ⟨ by simpa using Metric.lipschitz_infDist_pt S |> LipschitzWith.dist_le_mul |> fun h => h x y, by simpa using Metric.lipschitz_infDist_pt Sᶜ |> LipschitzWith.dist_le_mul |> fun h => h x y ⟩;
      simp_all +decide [ signedDistFun ];
      intro x y; specialize h_infDist_lip x y; rw [ dist_eq_norm ] at *; norm_num [ div_eq_inv_mul ] at *;
      exact abs_le.mpr ⟨ by linarith [ abs_le.mp h_infDist_lip.1, abs_le.mp ( show |Metric.infDist x Sᶜ - Metric.infDist y Sᶜ| ≤ dist x y from h_infDist_lip.2 ) ], by linarith [ abs_le.mp h_infDist_lip.1, abs_le.mp ( show |Metric.infDist x Sᶜ - Metric.infDist y Sᶜ| ≤ dist x y from h_infDist_lip.2 ) ] ⟩

/-
Separation bound: if u ∈ S with padding radius R, and v ∈ Sᶜ,
then |signedDistFun S u - signedDistFun S v| ≥ R/2.
-/
lemma signedDist_separation {S : Set X} {u v : X} {R : ℝ}
    (hR : 0 ≤ R) (hu_in : u ∈ S) (hu_pad : Metric.closedBall u R ⊆ S)
    (hv_out : v ∈ Sᶜ) :
    |signedDistFun S u - signedDistFun S v| ≥ R / 2 := by
      -- Since $u \in S$, we have $\text{infDist}(u, S) = 0$ and $\text{infDist}(u, S^c) \geq R$.
      have h_infDist_u_S : Metric.infDist u S = 0 := by
        exact Metric.infDist_zero_of_mem hu_in
      have h_infDist_u_Sc : Metric.infDist u Sᶜ ≥ R := by
        contrapose! hu_pad;
        rw [ Metric.infDist_lt_iff ] at hu_pad;
        · exact Set.not_subset.2 ⟨ hu_pad.choose, Metric.mem_closedBall'.2 hu_pad.choose_spec.2.le, hu_pad.choose_spec.1 ⟩;
        · exact ⟨ v, hv_out ⟩
      have h_infDist_v_Sc : Metric.infDist v Sᶜ = 0 := by
        exact Metric.infDist_zero_of_mem hv_out
      have h_infDist_v_S : Metric.infDist v S ≥ 0 := by
        exact Metric.infDist_nonneg;
      unfold signedDistFun; rw [ abs_of_nonpos ] <;> linarith;

/-- signedDistFun negation: signedDistFun Sᶜ = -signedDistFun S. -/
lemma signedDistFun_compl (S : Set X) (x : X) :
    signedDistFun Sᶜ x = -signedDistFun S x := by
  simp [signedDistFun, compl_compl]; ring

/-- |f(u)-f(v)| is symmetric under complement. -/
lemma signedDist_abs_compl (S : Set X) (u v : X) :
    |signedDistFun Sᶜ u - signedDistFun Sᶜ v| =
    |signedDistFun S u - signedDistFun S v| := by
  simp only [signedDistFun_compl]
  rw [show -signedDistFun S u - -signedDistFun S v = -(signedDistFun S u - signedDistFun S v) by ring]
  rw [abs_neg]

/-! ## Case II: No Large Ball (Padded Decomposition) -/

/-
**Case II**: Given a partition P₀ that is D-bounded with a large padded set,
and no ball of radius D having ≥ n/10 points, the signed distance function for
a well-chosen coloring achieves Σ|f-f| ≥ 9n²D/(80α).
-/
theorem embedding_case_two
    {α D : ℝ} (hα : 1 ≤ α) (hD : 0 < D) (hn : 2 ≤ Fintype.card X)
    (hsmall : ∀ x₀ : X,
      (Finset.univ.filter (fun x => dist x x₀ ≤ D)).card * 10 < Fintype.card X)
    (P₀ : Partition X) (hbdd : P₀.IsBounded D)
    (hpad : ∀ z : X, Metric.closedBall z (D / α) ⊆ P₀.cluster z →
      z ∈ Finset.univ.filter (fun z => Metric.closedBall z (D / α) ⊆ P₀.cluster z))
    (hH₀_large : 2 * (Finset.univ.filter
        (fun z => Metric.closedBall z (D / α) ⊆ P₀.cluster z)).card ≥
        Fintype.card X) :
    ∃ (f : X → ℝ), LipschitzWith 1 f ∧
      9 * (Fintype.card X : ℝ) ^ 2 * (D / α) ≤
        80 * (∑ u : X, ∑ v : X, |f u - f v|) := by
          -- Let H₀ be the padded set and R = D/α.
          set H₀ := {z : X | Metric.closedBall z (D / α) ⊆ P₀.cluster z}
          set R := D / α with hR_def
          have hH₀_card : H₀.toFinset.card ≥ Fintype.card X / 2 := by
            exact Nat.div_le_of_le_mul <| by simpa [ ← two_mul ] using hH₀_large;
          -- For each subset of labels S_labels ⊆ (image P₀ univ), define T = {x | P₀ x ∈ S_labels}. Use f = signedDistFun T.
          obtain ⟨S_labels, hS_labels⟩ : ∃ S_labels : Finset (ℕ), S_labels ⊆ Finset.image P₀ Finset.univ ∧ (∑ u ∈ H₀.toFinset, ∑ v ∈ Finset.univ.filter (fun x => P₀ x ∉ S_labels ∧ P₀ u ∈ S_labels) ∪ Finset.univ.filter (fun x => P₀ x ∈ S_labels ∧ P₀ u ∉ S_labels), (R / 2)) ≥ (9 * (Fintype.card X : ℝ)^2 * R) / 80 := by
            have h_avg : (∑ S_labels ∈ Finset.powerset (Finset.image P₀.label Finset.univ), (∑ u ∈ H₀.toFinset, ∑ v ∈ Finset.univ.filter (fun x => P₀ x ∉ S_labels ∧ P₀ u ∈ S_labels) ∪ Finset.univ.filter (fun x => P₀ x ∈ S_labels ∧ P₀ u ∉ S_labels), (R / 2))) ≥ (9 * (Fintype.card X : ℝ)^2 * R) / 80 * 2 ^ (Finset.card (Finset.image P₀.label Finset.univ)) := by
              have h_avg : ∀ u ∈ H₀.toFinset, (∑ S_labels ∈ Finset.powerset (Finset.image P₀.label Finset.univ), (∑ v ∈ Finset.univ.filter (fun x => P₀ x ∉ S_labels ∧ P₀ u ∈ S_labels) ∪ Finset.univ.filter (fun x => P₀ x ∈ S_labels ∧ P₀ u ∉ S_labels), (R / 2))) ≥ (9 * (Fintype.card X : ℝ) * R) / 40 * 2 ^ (Finset.card (Finset.image P₀.label Finset.univ)) := by
                intro u hu
                have h_avg_u : (∑ S_labels ∈ Finset.powerset (Finset.image P₀.label Finset.univ), (∑ v ∈ Finset.univ.filter (fun x => P₀ x ∉ S_labels ∧ P₀ u ∈ S_labels) ∪ Finset.univ.filter (fun x => P₀ x ∈ S_labels ∧ P₀ u ∉ S_labels), (R / 2))) = (∑ v ∈ Finset.univ, if P₀ v = P₀ u then 0 else (R / 2) * 2 ^ (Finset.card (Finset.image P₀.label Finset.univ) - 1)) := by
                  have h_avg_u : ∀ v ∈ Finset.univ, (∑ S_labels ∈ Finset.powerset (Finset.image P₀.label Finset.univ), if (P₀ v ≠ P₀ u) ∧ (P₀ v ∈ S_labels ∧ P₀ u ∉ S_labels ∨ P₀ v ∉ S_labels ∧ P₀ u ∈ S_labels) then (R / 2) else 0) = if P₀ v = P₀ u then 0 else (R / 2) * 2 ^ (Finset.card (Finset.image P₀.label Finset.univ) - 1) := by
                    intro v hv
                    by_cases huv : P₀.label v = P₀.label u;
                    · simp [huv];
                    · simp +decide [ huv, Finset.sum_ite ];
                      rw [ mul_comm ];
                      rw [ show ( Finset.filter ( fun x => P₀.label v ∈ x ∧ P₀.label u ∉ x ∨ P₀.label v ∉ x ∧ P₀.label u ∈ x ) ( Finset.powerset ( Finset.image P₀.label Finset.univ ) ) ) = Finset.biUnion ( Finset.powerset ( Finset.image P₀.label Finset.univ \ { P₀.label v, P₀.label u } ) ) ( fun s => { s ∪ { P₀.label v }, s ∪ { P₀.label u } } ) from ?_, Finset.card_biUnion ];
                      · rw [ Finset.sum_congr rfl fun x hx => Finset.card_pair <| ?_ ];
                        · simp +decide [ Finset.card_sdiff, huv ];
                          rw [ ← pow_succ, tsub_add_eq_add_tsub ];
                          · exact Or.inl rfl;
                          · exact Finset.one_lt_card.2 ⟨ P₀.label v, Finset.mem_image_of_mem _ ( Finset.mem_univ _ ), P₀.label u, Finset.mem_image_of_mem _ ( Finset.mem_univ _ ), huv ⟩;
                        · simp_all +decide [ Finset.ext_iff ];
                          exact ⟨ P₀.label v, by have := hx; have := @this ( P₀.label v ) ; aesop ⟩;
                      · intro s hs t ht hst; simp_all +decide [ Finset.disjoint_left ] ;
                        simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff, Set.subset_def ];
                      · ext; simp [Finset.mem_biUnion, Finset.mem_powerset];
                        constructor;
                        · rintro ⟨ h₁, h₂ | h₂ ⟩;
                          · use ‹Finset ℕ› \ {P₀.label v};
                            grind;
                          · use ‹Finset ℕ› \ {P₀.label u};
                            grind;
                        · grind;
                  rw [ ← Finset.sum_congr rfl h_avg_u, Finset.sum_comm ];
                  simp +decide [ Finset.sum_ite ];
                  congr! 3;
                  congr! 1;
                  grind;
                have h_avg_u : (∑ v ∈ Finset.univ, if P₀ v = P₀ u then 0 else (R / 2) * 2 ^ (Finset.card (Finset.image P₀.label Finset.univ) - 1)) ≥ (9 * (Fintype.card X : ℝ) * R) / 40 * 2 ^ (Finset.card (Finset.image P₀.label Finset.univ)) := by
                  have h_card : (Finset.univ.filter (fun v => P₀ v = P₀ u)).card ≤ (Fintype.card X : ℝ) / 10 := by
                    have h_card : (Finset.univ.filter (fun v => P₀ v = P₀ u)).card ≤ (Finset.univ.filter (fun v => dist v u ≤ D)).card := by
                      refine' Finset.card_le_card _;
                      intro v hv; have := hbdd u; simp_all +decide [ Metric.ediam_le_iff ] ;
                      simpa [ edist_dist ] using ENNReal.toReal_le_of_le_ofReal hD.le ( this v hv u rfl );
                    rw [ le_div_iff₀ ] <;> norm_cast ; linarith [ hsmall u ]
                  simp_all +decide [ Finset.sum_ite ];
                  rw [ show ( Finset.univ.filter fun x => ¬P₀.label x = P₀.label u ) = Finset.univ \ ( Finset.univ.filter fun x => P₀.label x = P₀.label u ) by ext; simp +decide, Finset.card_sdiff ] ; norm_num;
                  rw [ Nat.cast_sub ( show Finset.card ( Finset.filter ( fun x => P₀.label x = P₀.label u ) Finset.univ ) ≤ Fintype.card X from le_trans ( Finset.card_filter_le _ _ ) ( by simp +decide ) ) ] ; rcases k : Finset.card ( Finset.image P₀.label Finset.univ ) with ( _ | k ) <;> simp_all +decide [ pow_succ' ] ; ring_nf at * ; norm_num at *;
                  nlinarith [ show 0 < D * α⁻¹ * 2 ^ ‹_› by positivity ];
                linarith;
              rw [ Finset.sum_comm ];
              refine' le_trans _ ( Finset.sum_le_sum h_avg );
              simp +zetaDelta at *;
              field_simp;
              norm_cast ; linarith;
            contrapose! h_avg;
            refine' lt_of_lt_of_le ( Finset.sum_lt_sum_of_nonempty ( Finset.card_pos.mp _ ) fun S hS => h_avg S ( Finset.mem_powerset.mp hS ) ) _;
            · exact Finset.card_pos.mpr ⟨ ∅, Finset.mem_powerset.mpr <| Finset.empty_subset _ ⟩;
            · simp +decide [ mul_comm ];
          refine' ⟨ fun x => signedDistFun ( { x | P₀.label x ∈ S_labels } ) x, _, _ ⟩;
          · exact signedDistFun_lipschitz _;
          · -- For each $u \in H₀$, we have $|f(u) - f(v)| \geq R/2$ for all $v$ such that $P₀(v) \notin S_labels$ and $P₀(u) \in S_labels$, or vice versa.
            have h_dist : ∀ u ∈ H₀.toFinset, ∑ v ∈ Finset.univ.filter (fun x => P₀.label x ∉ S_labels ∧ P₀.label u ∈ S_labels) ∪ Finset.univ.filter (fun x => P₀.label x ∈ S_labels ∧ P₀.label u ∉ S_labels), |signedDistFun {x | P₀.label x ∈ S_labels} u - signedDistFun {x | P₀.label x ∈ S_labels} v| ≥ ∑ v ∈ Finset.univ.filter (fun x => P₀.label x ∉ S_labels ∧ P₀.label u ∈ S_labels) ∪ Finset.univ.filter (fun x => P₀.label x ∈ S_labels ∧ P₀.label u ∉ S_labels), (R / 2) := by
              intro u hu
              apply Finset.sum_le_sum
              intro v hv
              have h_dist : |signedDistFun {x | P₀.label x ∈ S_labels} u - signedDistFun {x | P₀.label x ∈ S_labels} v| ≥ R / 2 := by
                by_cases huv : P₀.label u ∈ S_labels <;> by_cases hvu : P₀.label v ∈ S_labels <;> simp_all +decide;
                · apply_rules [ signedDist_separation ];
                  · positivity;
                  · intro x hx; have := hu hx; aesop;
                · have h_dist : |signedDistFun {x | P₀.label x ∈ S_labels}ᶜ u - signedDistFun {x | P₀.label x ∈ S_labels}ᶜ v| ≥ R / 2 := by
                    apply_rules [ signedDist_separation ];
                    · positivity;
                    · intro x hx; have := hu hx; simp_all +decide [ Partition.cluster ] ;
                    · aesop;
                  convert h_dist.le using 1 ; rw [ signedDist_abs_compl ]
              exact h_dist;
            have h_sum_dist : ∑ u ∈ H₀.toFinset, ∑ v, |signedDistFun {x | P₀.label x ∈ S_labels} u - signedDistFun {x | P₀.label x ∈ S_labels} v| ≥ ∑ u ∈ H₀.toFinset, ∑ v ∈ Finset.univ.filter (fun x => P₀.label x ∉ S_labels ∧ P₀.label u ∈ S_labels) ∪ Finset.univ.filter (fun x => P₀.label x ∈ S_labels ∧ P₀.label u ∉ S_labels), (R / 2) := by
              exact Finset.sum_le_sum fun u hu => le_trans ( h_dist u hu ) ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_univ _ ) fun _ _ _ => abs_nonneg _ );
            refine' le_trans _ ( mul_le_mul_of_nonneg_left ( h_sum_dist.trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_univ _ ) fun _ _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _ ) ) ( by positivity ) );
            grind +splitImp

/-! ## Bartal's Modulus Bound -/

/-- **Average Distortion Embedding**: Every n-point metric space admits a
non-expansive embedding into ℝ with average distortion O(log n).

More precisely, for any n-point metric space (X, d), there exists a 1-Lipschitz
function f : X → ℝ such that `pairDistSum X ≤ 1280 · log(n) · embeddingSum f`. -/
theorem nonexpansive_avg_distortion_embedding
    (X : Type*) [MetricSpace X] [Fintype X] :
    ∃ (f : X → ℝ), LipschitzWith 1 f ∧
      (∑ u : X, ∑ v : X, dist u v) ≤
        1280 * Real.log (Fintype.card X) * (∑ u : X, ∑ v : X, |f u - f v|) := by
          by_cases h_card : Fintype.card X ≤ 1
          generalize_proofs at *; (
          refine' ⟨ fun _ => 0, _, _ ⟩ <;> norm_num [ LipschitzWith ];
          cases h_card.eq_or_lt <;> simp_all +decide [ Fintype.card_le_one_iff ];
          · rw [ Fintype.card_eq_one_iff ] at * ; aesop;
          · rw [ Fintype.card_eq_zero_iff ] at * ; aesop ( simp_config := { singlePass := true } ) ;);
          by_contra! h_contra;
          obtain ⟨x₀, D, hD_pos, hD⟩ : ∃ x₀ : X, ∃ D : ℝ, 0 < D ∧ 4 * (Fintype.card X : ℝ)^2 * D ≤ ∑ u : X, ∑ v : X, dist u v ∧ (Finset.univ.filter (fun x => dist x x₀ ≤ D)).card * 10 ≥ Fintype.card X ∨ ∀ x₀ : X, (Finset.univ.filter (fun x => dist x x₀ ≤ (∑ u : X, ∑ v : X, dist u v) / (4 * (Fintype.card X : ℝ)^2))).card * 10 < Fintype.card X := by
            by_cases h_large_ball : ∃ x₀ : X, (Finset.univ.filter (fun x => dist x x₀ ≤ (∑ u : X, ∑ v : X, dist u v) / (4 * (Fintype.card X : ℝ)^2))).card * 10 ≥ Fintype.card X;
            · obtain ⟨ x₀, hx₀ ⟩ := h_large_ball
              use x₀, (∑ u : X, ∑ v : X, dist u v) / (4 * (Fintype.card X : ℝ)^2);
              refine' Or.inl ⟨ div_pos _ _, _, hx₀ ⟩ <;> norm_num at *;
              · exact lt_of_le_of_lt ( mul_nonneg ( mul_nonneg ( by norm_num ) ( Real.log_nonneg ( Nat.one_le_cast.mpr h_card.le ) ) ) ( Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _ ) ) ( h_contra ( fun _ => 0 ) ( by norm_num [ LipschitzWith ] ) );
              · positivity;
              · rw [ mul_div_cancel₀ _ ( by positivity ) ];
            · exact ⟨ Classical.choose ( Finset.card_pos.mp ( pos_of_gt ( not_le.mp h_card ) ) ), ( ∑ u : X, ∑ v : X, dist u v ) / ( 4 * ( Fintype.card X : ℝ ) ^ 2 ), Or.inr fun x₀ => lt_of_not_ge fun h => h_large_ball ⟨ x₀, h ⟩ ⟩;
          · obtain ⟨f, hf_lip, hf_dist⟩ : ∃ f : X → ℝ, LipschitzWith 1 f ∧ (∑ u : X, ∑ v : X, dist u v) ≤ 40 * (∑ u : X, ∑ v : X, |f u - f v|) := by
              apply embedding_case_one x₀ D (by linarith) (by linarith) (by linarith)
            generalize_proofs at *; (
            have := h_contra f hf_lip
            generalize_proofs at *; (
            nlinarith [ show ( Fintype.card X : ℝ ) ≥ 2 by exact_mod_cast not_le.mp h_card, Real.log_two_gt_d9, Real.log_le_log ( by norm_num ) ( show ( Fintype.card X : ℝ ) ≥ 2 by exact_mod_cast not_le.mp h_card ), show ( ∑ u : X, ∑ v : X, |f u - f v| ) ≥ 0 by exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _ ] ;));
          · obtain ⟨P₀, hP₀_bdd, hP₀_pad⟩ : ∃ P₀ : Partition X, P₀.IsBounded ((∑ u : X, ∑ v : X, dist u v) / (4 * (Fintype.card X : ℝ)^2)) ∧ 2 * (Finset.univ.filter (fun z => Metric.closedBall z ((∑ u : X, ∑ v : X, dist u v) / (4 * (Fintype.card X : ℝ)^2) / (16 * Real.log (Fintype.card X))) ⊆ P₀.cluster z)).card ≥ Fintype.card X := by
              apply bartal_has_padded_modulus X ((∑ u : X, ∑ v : X, dist u v) / (4 * (Fintype.card X : ℝ)^2)) (by
              refine' div_pos _ _ <;> norm_cast;
              · exact lt_of_le_of_lt ( by positivity ) ( h_contra ( fun _ => 0 ) ( by simp +decide [ LipschitzWith ] ) );
              · nlinarith);
            obtain ⟨f, hf_lip, hf_dist⟩ : ∃ f : X → ℝ, LipschitzWith 1 f ∧ 9 * (Fintype.card X : ℝ) ^ 2 * ((∑ u : X, ∑ v : X, dist u v) / (4 * (Fintype.card X : ℝ)^2) / (16 * Real.log (Fintype.card X))) ≤ 80 * (∑ u : X, ∑ v : X, |f u - f v|) := by
              apply_rules [ embedding_case_two ];
              · exact le_trans ( by norm_num ) ( mul_le_mul_of_nonneg_left ( Real.log_two_gt_d9.le.trans ( Real.log_le_log ( by norm_num ) ( Nat.cast_le.mpr ( show Fintype.card X ≥ 2 by linarith ) ) ) ) ( by norm_num ) );
              · refine' div_pos _ _ <;> norm_num;
                · contrapose! h_contra;
                  exact ⟨ fun _ => 0, by norm_num [ LipschitzWith ], by simpa using h_contra.trans ( by positivity ) ⟩;
                · exact sq_pos_of_pos ( Nat.cast_pos.mpr ( pos_of_gt ( not_le.mp h_card ) ) );
              · linarith;
              · aesop;
            have := h_contra f hf_lip;
            field_simp at hf_dist;
            rw [ div_le_iff₀ ] at hf_dist;
            · nlinarith [ show ( Fintype.card X : ℝ ) ≥ 2 by norm_cast; linarith, show ( ∑ u : X, ∑ v : X, dist u v ) ≥ 0 by exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg ];
            · exact mul_pos ( Nat.cast_pos.mpr ( pos_of_gt ( not_le.mp h_card ) ) ) ( Real.log_pos ( Nat.one_lt_cast.mpr ( lt_of_not_ge h_card ) ) )

end

end PaddedDecomposition
