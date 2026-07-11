/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-! # Algebraic lemmas for the sparse cover → padded decomposition proof

This file contains the key algebraic inequalities used in the padding probability
bound from Filtser's construction.

## Key inequalities

* `key_ineq_s_over_exp`: s/(e^l - 1) ≤ e^{-2γl} for l = 2 + 2 ln s, γ ≤ 1/4, s ≥ 1
* `padding_prob_bound`: (1-α)(1+α) = 1 - α² where α = e^{-2γl}
-/

open Real

noncomputable section

/-! ## Basic exponential / logarithm inequalities -/

/-
e^x - 1 ≥ e^(x-1) for x ≥ 1.
    Equivalently, e^x ≥ 1 + e^(x-1). Since e^(x-1) = e^x/e, this is
    e^x ≥ 1 + e^x/e, i.e., e^x(1 - 1/e) ≥ 1, i.e., e^x ≥ e/(e-1).
    For x ≥ 1: e^x ≥ e ≥ e/(e-1) ≈ 1.58.
-/
lemma exp_sub_one_ge_exp_sub {x : ℝ} (hx : 1 ≤ x) : exp x - 1 ≥ exp (x - 1) := by
  norm_num [ Real.exp_sub ];
  rw [ div_le_iff₀ ( Real.exp_pos _ ) ];
  nlinarith [ Real.add_one_le_exp 1, Real.exp_pos x, Real.exp_le_exp.2 hx ]

/-- For l = 2 + 2 * ln s with s ≥ 1, we have l ≥ 2 -/
lemma lambda_ge_two (s : ℕ) (hs : 1 ≤ s) : 2 + 2 * Real.log (↑s : ℝ) ≥ 2 := by
  linarith [Real.log_nonneg (by exact_mod_cast hs : (1 : ℝ) ≤ ↑s)]

/-- For l = 2 + 2 * ln s with s ≥ 1, we have e^(l/2 - 1) = s -/
lemma exp_half_lambda_sub_one (s : ℕ) (hs : 1 ≤ s) :
    exp ((2 + 2 * Real.log ↑s) / 2 - 1) = ↑s := by
  have hs' : (0 : ℝ) < ↑s := Nat.cast_pos.mpr (by omega)
  rw [show (2 + 2 * Real.log ↑s) / 2 - 1 = Real.log ↑s by ring]
  exact exp_log hs'

/-- -2γl + l - 1 ≥ l/2 - 1 when γ ≤ 1/4 -/
lemma exp_exponent_ineq (gam l : ℝ) (hgam : gam ≤ 1 / 4) (hl : 0 ≤ l) :
    -(2 * gam * l) + (l - 1) ≥ l / 2 - 1 := by
  nlinarith

/-
The key inequality: s / (e^l - 1) ≤ e^{-2γl} for l = 2 + 2 ln s, γ ∈ [0, 1/4], s ≥ 1.

The proof follows the paper:
  e^{-2γl} = e^{-2γl}(e^l - 1)/(e^l - 1)
            ≥ e^{-2γl} · e^{l-1} / (e^l - 1)     [since e^l - 1 ≥ e^{l-1}]
            ≥ e^{l/2 - 1} / (e^l - 1)              [since -2γl + l - 1 ≥ l/2 - 1 when γ ≤ 1/4]
            = s / (e^l - 1)                          [since e^{l/2-1} = s]
-/
lemma key_ineq_s_over_exp (s : ℕ) (hs : 1 ≤ s) (gam : ℝ) (_hgam0 : 0 ≤ gam) (hgam : gam ≤ 1/4) :
    ↑s / (exp (2 + 2 * Real.log ↑s) - 1) ≤ exp (-(2 * gam * (2 + 2 * Real.log ↑s))) := by
  rw [ div_le_iff₀ ];
  · -- Use the chain from the paper: e^{-2γl} ≥ e^{-2γl} · e^{l-1}/(e^l-1) ≥ e^{l/2-1}/(e^l-1) = s/(e^l-1), where l = 2+2ln s.
    have h_chain : Real.exp (-(2 * gam * (2 + 2 * Real.log s))) * (Real.exp (2 + 2 * Real.log s) - 1) ≥ Real.exp (-(2 * gam * (2 + 2 * Real.log s))) * Real.exp ((2 + 2 * Real.log s) - 1) := by
      exact mul_le_mul_of_nonneg_left ( by linarith [ exp_sub_one_ge_exp_sub ( show 1 ≤ 2 + 2 * Real.log s by linarith [ Real.log_nonneg ( show ( s : ℝ ) ≥ 1 by norm_cast ) ] ) ] ) ( Real.exp_nonneg _ );
    refine le_trans ?_ h_chain ; norm_num [ ← Real.exp_add ] ; ring_nf;
    rw [ ← Real.log_le_iff_le_exp ( by positivity ) ] ; nlinarith [ Real.log_nonneg ( by norm_cast : ( 1 :ℝ ) ≤ s ) ] ;
  · exact sub_pos_of_lt ( by norm_num; positivity )

/-- The padding probability bound: 1 - (1-α)(1+α) = α² -/
lemma one_sub_mul_eq_sq (al : ℝ) : 1 - (1 - al) * (1 + al) = al ^ 2 := by ring

/-- The final padding probability after scaling -/
lemma padding_exp_bound (bet gam : ℝ) (s : ℕ) (_hs : 1 ≤ s)
    (_hbet : 0 < bet) (_hgam0 : 0 ≤ gam) (_hgam : gam ≤ 1 / (4 * bet)) :
    exp (-(4 * bet * (2 + 2 * Real.log ↑s) * gam)) ≤
    exp (-(2 * (bet * gam) * (2 + 2 * Real.log ↑s))) ^ 2 := by
  rw [show -(2 * (bet * gam) * (2 + 2 * Real.log ↑s)) = -(2 * bet * gam * (2 + 2 * Real.log ↑s)) by ring]
  rw [sq, ← exp_add]
  apply exp_le_exp_of_le
  linarith

end