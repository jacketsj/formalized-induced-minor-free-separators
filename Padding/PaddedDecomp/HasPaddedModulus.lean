/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Padding.PaddedDecompDefs
import Padding.PaddedDecomp.Bartal
import Padding.PaddedDecomp.BartalHelpers

/-! # Proofs of Padded Modulus Bounds

This file contains the proofs of:
- `has_padded_modulus_linear`: every finite metric space has padded modulus O(n)
- `bartal_has_padded_modulus`: every finite metric space has padded modulus O(log n)

The definitions `HasPaddedModulus` and `HasPaddedModulus.mono` are in `Defs.lean`.
-/

open PaddedDecomposition MeasureTheory Metric Set Real Finset BigOperators

namespace PaddedDecomposition

noncomputable section

open Classical

/-- Using the connected component partition, every finite metric space has padded modulus
at most `2 * (n - 1)`. -/
theorem has_padded_modulus_linear (X : Type*) [MetricSpace X] [Fintype X]
    (hn : 2 ≤ Fintype.card X) :
    HasPaddedModulus X (2 * ((Fintype.card X : ℝ) - 1)) := by
  intro Δ hΔ
  have hn1_pos : (0 : ℝ) < (Fintype.card X : ℝ) - 1 := by
    have : (1 : ℝ) < Fintype.card X := by exact_mod_cast show 1 < Fintype.card X by omega
    linarith
  set r := Δ / (2 * ((Fintype.card X : ℝ) - 1)) with hr_def
  have hr_pos : 0 < r := by positivity
  refine ⟨componentPart (X := X) r, ?_, ?_⟩
  · apply componentPart_isBounded r Δ (le_of_lt hr_pos)
    calc ((Fintype.card X : ℝ) - 1) * r
        = ((Fintype.card X : ℝ) - 1) * (Δ / (2 * ((Fintype.card X : ℝ) - 1))) := rfl
      _ = Δ / 2 := by field_simp
      _ ≤ Δ := by linarith
  · suffices h : Finset.univ.filter (fun z : X =>
        Metric.closedBall z r ⊆ (componentPart (X := X) r).cluster z) = Finset.univ by
      have : Finset.univ.filter (fun z : X =>
          Metric.closedBall z (Δ / (2 * (↑(Fintype.card X) - 1))) ⊆
            (componentPart (X := X) r).cluster z) = Finset.univ := h
      rw [this, Finset.card_univ]; omega
    ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact componentPart_closedBall_subset r z

/-! ## Main Existence Lemma -/

variable {X : Type*} [MetricSpace X] [Fintype X]

set_option maxHeartbeats 1600000

/-
For β > 0 with 2β ≤ Δ and 0 ≤ ρ ≤ β, if the weighted sum of ball ratios is ≥ n/2,
    then there exists a Δ-bounded partition with ≥ n/2 points padded at radius ρ.
-/
lemma exists_partition_of_sum_ratios (Δ β ρ : ℝ) (_hΔ : 0 < Δ) (hβ : 0 < β)
    (hρ : 0 ≤ ρ) (hρβ : ρ ≤ β) (hβΔ : 2 * β ≤ Δ)
    (h_sum : (∑ z : X, ((Finset.univ.filter (fun w : X => dist z w ≤ β - ρ)).card : ℝ) /
      (Finset.univ.filter (fun w : X => dist z w ≤ β + ρ)).card) ≥ Fintype.card X / 2) :
    ∃ P : Partition X, P.IsBounded Δ ∧
      2 * (Finset.univ.filter (fun z : X =>
        Metric.closedBall z ρ ⊆ P.cluster z)).card ≥ Fintype.card X := by
  -- Applying the greedy padding count lemma to each point $z$ in $X$.
  have h_count : ∀ z : X, (Finset.univ.filter (fun w : X => dist z w ≤ β - ρ)).card * (Fintype.card (Fin (Fintype.card X) ≃ X)) ≤ (Finset.univ.filter (fun σ : Fin (Fintype.card X) ≃ X => Metric.closedBall z ρ ⊆ (greedyBallPart' σ β hβ.le).cluster z)).card * (Finset.univ.filter (fun w : X => dist z w ≤ β + ρ)).card := by
    intro z;
    convert greedy_padding_count' β ρ hβ hρ hρβ z using 1;
  -- By summing over all points $z$ in $X$, we get the desired inequality.
  have h_sum_count : ∑ z : X, (Finset.univ.filter (fun σ : Fin (Fintype.card X) ≃ X => Metric.closedBall z ρ ⊆ (greedyBallPart' σ β hβ.le).cluster z)).card ≥ (Fintype.card X : ℝ) / 2 * (Fintype.card (Fin (Fintype.card X) ≃ X)) := by
    refine' le_trans ( mul_le_mul_of_nonneg_right h_sum _ ) _;
    · grind;
    · push_cast [ Finset.sum_mul _ _ _ ];
      refine' Finset.sum_le_sum fun z _ => _;
      rw [ div_mul_eq_mul_div, div_le_iff₀ ] <;> norm_cast;
      · exact h_count z;
      · exact Finset.card_pos.mpr ⟨ z, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, by simpa using by linarith ⟩ ⟩;
  -- By the pigeonhole principle, there exists a permutation σ such that the number of padded points is at least the average.
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin (Fintype.card X) ≃ X, (Finset.univ.filter (fun z : X => Metric.closedBall z ρ ⊆ (greedyBallPart' σ β hβ.le).cluster z)).card ≥ (Fintype.card X : ℝ) / 2 := by
    contrapose! h_sum_count;
    convert Finset.sum_lt_sum_of_nonempty ( Finset.univ_nonempty ) fun σ _ => h_sum_count σ using 1;
    · rw [ Finset.sum_congr rfl fun _ _ => Finset.card_filter _ _ ];
      rw [ Finset.sum_comm ] ; simp +decide;
    · simp +decide [ mul_comm ];
    · exact ⟨ Fintype.equivOfCardEq <| by simp +decide ⟩;
  refine' ⟨ greedyBallPart' σ β hβ.le, _, _ ⟩;
  · exact greedyBallPart'_isBounded σ β Δ hβ.le hβΔ;
  · rw [ ge_iff_le, div_le_iff₀ ] at hσ <;> norm_cast at * ; linarith

/-
**Bartal's Padded Modulus Bound**: Every finite metric space on n points has
padded modulus at most `16 * ln(n)`.
-/
theorem bartal_has_padded_modulus (X : Type*) [MetricSpace X] [Fintype X] :
    HasPaddedModulus X (16 * Real.log (Fintype.card X)) := by
  by_cases h_card : Fintype.card X ≤ 1;
  · interval_cases _ : Fintype.card X <;> simp_all +decide;
    · rw [ Fintype.card_eq_zero_iff ] at *;
      exact fun Δ hΔ => ⟨ ⟨ fun _ => 0 ⟩, by simp +decide [ Partition.IsBounded ], by simp +decide [ Finset.card_eq_zero.mpr ] ⟩;
    · intro Δ hΔ; obtain ⟨ x, hx ⟩ := Fintype.card_eq_one_iff.mp ‹_›; use ⟨ fun _ => 0 ⟩ ; simp +decide [ hx ] ;
      exact ⟨ fun z => by rw [ show ( ⟨ fun _ => 0 ⟩ : Partition X ).cluster z = { z } by ext y; aesop ] ; simp +decide, by linarith ⟩;
  · intro Δ hΔ_pos
    set α := 16 * Real.log (Fintype.card X)
    set ρ := Δ / α
    set K := Nat.ceil (2 * Real.log (Fintype.card X))
    have hK : K ≥ 2 * Real.log (Fintype.card X) := by
      exact Nat.le_ceil _;
    -- For each $z$, the product $\prod_{j=0}^{K-1} \frac{|B(z, \beta_j + \rho)|}{|B(z, \beta_j - \rho)|}$ telescopes to $\frac{|B(z, \beta_{K-1} + \rho)|}{|B(z, \beta_0 - \rho)|} \leq n$.
    have h_prod : ∀ z : X, (∏ j ∈ Finset.range K, ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j * 2 * ρ) + ρ)).card : ℝ) / ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j * 2 * ρ) - ρ)).card : ℝ)) ≤ Fintype.card X := by
      intro z
      have h_prod_step : ∀ j ∈ Finset.range K, ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j * 2 * ρ) + ρ)).card : ℝ) / ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j * 2 * ρ) - ρ)).card : ℝ) = ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + (j + 1) * 2 * ρ) - ρ)).card : ℝ) / ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j * 2 * ρ) - ρ)).card : ℝ) := by
        intro j hj; ring_nf;
      rw [ Finset.prod_congr rfl h_prod_step ];
      have h_prod_telescope : ∀ n : ℕ, (∏ j ∈ Finset.range n, ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + (j + 1) * 2 * ρ) - ρ)).card : ℝ) / ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j * 2 * ρ) - ρ)).card : ℝ)) = ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + n * 2 * ρ) - ρ)).card : ℝ) / ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + 0 * 2 * ρ) - ρ)).card : ℝ) := by
        intro n
        induction' n with n ih;
        · simp +decide;
          rw [ div_self ] ; norm_cast ; exact ne_of_gt ( Finset.card_pos.mpr ⟨ z, by simp +decide [ dist_self ] ; linarith [ show ρ < Δ / 4 from by rw [ div_lt_iff₀ ( mul_pos ( by norm_num ) ( Real.log_pos ( Nat.one_lt_cast.mpr ( lt_of_not_ge h_card ) ) ) ) ] ; nlinarith [ show ( Fintype.card X : ℝ ) ≥ 2 by exact_mod_cast lt_of_not_ge h_card, Real.log_two_gt_d9, Real.log_le_log ( by norm_num ) ( show ( Fintype.card X : ℝ ) ≥ 2 by exact_mod_cast lt_of_not_ge h_card ) ] ] ⟩ );
        · rw [ Finset.prod_range_succ, ih ];
          rw [ mul_comm, div_mul_div_cancel₀ ] ; norm_num;
          simp +zetaDelta at *;
          use z;
          norm_num;
          exact le_add_of_le_of_nonneg ( div_le_div_of_nonneg_left ( by positivity ) ( by positivity ) ( by linarith [ Real.log_two_gt_d9, Real.log_le_log ( by positivity ) ( show ( Fintype.card X : ℝ ) ≥ 2 by norm_cast ) ] ) ) ( by positivity );
      rw [ h_prod_telescope ];
      refine' le_trans ( div_le_self ( Nat.cast_nonneg _ ) _ ) _;
      · refine' mod_cast Finset.card_pos.mpr ⟨ z, _ ⟩ ; norm_num;
        rw [ div_le_div_iff₀ ] <;> nlinarith [ show ( Fintype.card X : ℝ ) ≥ 2 by norm_cast; linarith, Real.log_two_gt_d9, Real.log_le_log ( by norm_num ) ( show ( Fintype.card X : ℝ ) ≥ 2 by norm_cast; linarith ) ];
      · exact_mod_cast Finset.card_le_univ _;
    -- Using the inequality $1 - x \leq -\ln(x)$ for $x > 0$, we get $\sum_{j=0}^{K-1} (1 - P_j(z)) \leq \sum_{j=0}^{K-1} (-\ln P_j(z)) = \ln(\prod_{j=0}^{K-1} \frac{1}{P_j(z)}) \leq \ln n$.
    have h_sum : ∀ z : X, (∑ j ∈ Finset.range K, (1 - ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j * 2 * ρ) - ρ)).card : ℝ) / ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j * 2 * ρ) + ρ)).card : ℝ))) ≤ Real.log (Fintype.card X) := by
      intro z
      have h_sum_step : (∑ j ∈ Finset.range K, (1 - ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j * 2 * ρ) - ρ)).card : ℝ) / ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j * 2 * ρ) + ρ)).card : ℝ))) ≤ Real.log (∏ j ∈ Finset.range K, ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j * 2 * ρ) + ρ)).card : ℝ) / ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j * 2 * ρ) - ρ)).card : ℝ)) := by
        have h_sum_step : ∀ j ∈ Finset.range K, (1 - ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j * 2 * ρ) - ρ)).card : ℝ) / ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j * 2 * ρ) + ρ)).card : ℝ)) ≤ Real.log ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j * 2 * ρ) + ρ)).card / ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j * 2 * ρ) - ρ)).card : ℝ)) := by
          intro j hj
          have h_pos : 0 < ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j * 2 * ρ) + ρ)).card : ℝ) / ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j * 2 * ρ) - ρ)).card : ℝ) := by
            refine' div_pos _ _ <;> norm_cast;
            · exact Finset.card_pos.mpr ⟨ z, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, by norm_num; positivity ⟩ ⟩;
            · refine' Finset.card_pos.mpr ⟨ z, _ ⟩ ; norm_num;
              exact le_add_of_le_of_nonneg ( div_le_div_of_nonneg_left ( by positivity ) ( by positivity ) ( by nlinarith [ show ( Fintype.card X : ℝ ) ≥ 2 by norm_cast; linarith, Real.log_two_gt_d9, Real.log_le_log ( by positivity ) ( show ( Fintype.card X : ℝ ) ≥ 2 by norm_cast; linarith ) ] ) ) ( by positivity );
          have := Real.log_le_sub_one_of_pos ( inv_pos.mpr h_pos );
          rw [ Real.log_inv ] at this ; norm_num at * ; linarith;
        rw [ Real.log_prod ];
        · exact Finset.sum_le_sum h_sum_step;
        · intro j hj
          have h_card_pos : 0 < (Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j * 2 * ρ) - ρ)).card := by
            refine' Finset.card_pos.mpr ⟨ z, _ ⟩ ; norm_num;
            exact le_add_of_le_of_nonneg ( div_le_div_of_nonneg_left ( by positivity ) ( by positivity ) ( by linarith [ show ( 16 : ℝ ) * Real.log ( Fintype.card X ) ≥ 4 by linarith [ show ( Real.log ( Fintype.card X ) : ℝ ) ≥ 1 / 4 by exact le_trans ( by norm_num ) ( Real.log_two_gt_d9.le.trans ( Real.log_le_log ( by norm_num ) ( Nat.cast_le.mpr ( show Fintype.card X ≥ 2 by linarith ) ) ) ) ] ] ) ) ( by positivity );
          exact ne_of_gt ( div_pos ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ⟨ z, by simp +decide [ show 0 ≤ Δ / 4 + ↑j * 2 * ρ + ρ by exact add_nonneg ( add_nonneg ( by positivity ) ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) zero_le_two ) ( div_nonneg hΔ_pos.le ( mul_nonneg ( by positivity ) ( Real.log_nonneg ( mod_cast by linarith ) ) ) ) ) ) ( div_nonneg hΔ_pos.le ( mul_nonneg ( by positivity ) ( Real.log_nonneg ( mod_cast by linarith ) ) ) ) ] ⟩ ) ) ( Nat.cast_pos.mpr h_card_pos ) );
      refine' le_trans h_sum_step ( Real.log_le_log _ ( h_prod z ) );
      refine' Finset.prod_pos fun j hj => div_pos _ _ <;> norm_cast <;> norm_num;
      · exact ⟨ z, by simp +decide [ show 0 ≤ Δ / 4 + j * 2 * ρ + ρ by exact add_nonneg ( add_nonneg ( by positivity ) ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) zero_le_two ) ( div_nonneg hΔ_pos.le ( mul_nonneg ( by positivity ) ( Real.log_nonneg ( mod_cast by linarith ) ) ) ) ) ) ( div_nonneg hΔ_pos.le ( mul_nonneg ( by positivity ) ( Real.log_nonneg ( mod_cast by linarith ) ) ) ) ] ⟩;
      · refine' ⟨ z, _ ⟩ ; norm_num;
        exact le_add_of_le_of_nonneg ( div_le_div_of_nonneg_left ( by positivity ) ( by positivity ) ( by nlinarith [ Real.log_two_gt_d9, Real.log_le_log ( by positivity ) ( show ( Fintype.card X : ℝ ) ≥ 2 by norm_cast; linarith ) ] ) ) ( by positivity );
    -- By pigeonhole, there exists a $j^*$ such that $\sum_{z} P_{j^*}(z) \geq \frac{n}{2}$.
    obtain ⟨j_star, hj_star⟩ : ∃ j_star ∈ Finset.range K, (∑ z : X, ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j_star * 2 * ρ) - ρ)).card : ℝ) / ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j_star * 2 * ρ) + ρ)).card : ℝ)) ≥ Fintype.card X / 2 := by
      have h_pigeonhole : (∑ j ∈ Finset.range K, (∑ z : X, ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j * 2 * ρ) - ρ)).card : ℝ) / ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j * 2 * ρ) + ρ)).card : ℝ))) ≥ Fintype.card X * K / 2 := by
        have h_pigeonhole : (∑ j ∈ Finset.range K, (∑ z : X, (1 - ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j * 2 * ρ) - ρ)).card : ℝ) / ((Finset.univ.filter (fun w => dist z w ≤ (Δ / 4 + j * 2 * ρ) + ρ)).card : ℝ)))) ≤ Fintype.card X * Real.log (Fintype.card X) := by
          rw [ Finset.sum_comm ];
          exact le_trans ( Finset.sum_le_sum fun _ _ => h_sum _ ) ( by simp +decide );
        norm_num +zetaDelta at *;
        nlinarith [ show ( Fintype.card X : ℝ ) ≥ 2 by norm_cast, Real.log_nonneg ( show ( Fintype.card X : ℝ ) ≥ 1 by norm_cast; linarith ) ];
      contrapose! h_pigeonhole;
      convert Finset.sum_lt_sum_of_nonempty ( Finset.nonempty_of_ne_empty _ ) h_pigeonhole using 1 <;> norm_num ; ring;
      exact Nat.ne_of_gt <| Nat.ceil_pos.mpr <| mul_pos zero_lt_two <| Real.log_pos <| Nat.one_lt_cast.mpr <| lt_of_not_ge h_card;
    convert exists_partition_of_sum_ratios Δ ( Δ / 4 + j_star * 2 * ρ ) ρ hΔ_pos _ _ _ _ hj_star.2 using 1 <;> norm_num at *;
    · exact add_pos_of_pos_of_nonneg ( by positivity ) ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) zero_le_two ) ( div_nonneg hΔ_pos.le ( mul_nonneg ( by positivity ) ( Real.log_nonneg ( mod_cast h_card.le ) ) ) ) );
    · exact div_nonneg hΔ_pos.le ( mul_nonneg ( by norm_num ) ( Real.log_nonneg ( mod_cast h_card.le ) ) );
    · exact le_add_of_le_of_nonneg ( div_le_div_of_nonneg_left hΔ_pos.le ( by positivity ) ( by nlinarith [ Real.log_two_gt_d9, Real.log_le_log ( by positivity ) ( show ( Fintype.card X : ℝ ) ≥ 2 by norm_cast ) ] ) ) ( by positivity );
    · simp +zetaDelta at *;
      field_simp;
      rw [ add_div', mul_div, div_le_iff₀ ] <;> nlinarith [ Real.log_pos ( show ( Fintype.card X : ℝ ) > 1 by norm_cast ), show ( j_star : ℝ ) + 1 ≤ ⌈2 * Real.log ( Fintype.card X ) ⌉₊ by exact_mod_cast hj_star.1, Nat.ceil_lt_add_one ( show 0 ≤ 2 * Real.log ( Fintype.card X ) by positivity ) ]

end

end PaddedDecomposition
