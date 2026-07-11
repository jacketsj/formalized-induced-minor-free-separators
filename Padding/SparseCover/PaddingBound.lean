/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.SparseCover.PaddingProof
import Mathlib

/-! # Padding Probability Bound -/

open Real

noncomputable section

/-
The final padding probability is at least `e^{-4βγλ}`.
-/
theorem padding_prob_bound_abstract
    (β γ : ℝ) (s : ℕ)
    (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / (4 * β)) (hs : 1 ≤ s)
    (sum_F : ℝ) (hF_le : sum_F ≤ 1)
    (sum_Q : ℝ)
    (hQ_bound : sum_Q ≤
      (1 - exp (-(2 * β * γ * (2 + 2 * log ↑s)))) *
      (sum_F + ↑s / (exp (2 + 2 * log ↑s) - 1)))
    (P_good : ℝ) (hPg : P_good = 1 - sum_Q) :
    P_good ≥ exp (-(4 * β * (2 + 2 * log ↑s) * γ)) := by
      -- Set l = 2 + 2 * log s, α = exp(-(2*β*γ*l)).
      set l := 2 + 2 * Real.log s
      set α := Real.exp (-(2 * β * γ * l));
      -- By key_ineq_s_over_exp: s/(exp l - 1) ≤ exp(-(2*(β*γ)*(2+2*log s))) = α (with gam := β*γ).
      have h_key : (s : ℝ) / (Real.exp l - 1) ≤ α := by
        convert key_ineq_s_over_exp s hs ( β * γ ) ( by positivity ) ( by rw [ le_div_iff₀ ] at * <;> nlinarith ) using 1 ; ring_nf;
        exact congr_arg Real.exp ( by ring );
      rw [ show ( - ( 4 * β * l * γ ) ) = - ( 2 * β * γ * l ) + - ( 2 * β * γ * l ) by ring, Real.exp_add ];
      nlinarith [ Real.exp_pos ( - ( 2 * β * γ * l ) ), Real.exp_le_one_iff.mpr ( show - ( 2 * β * γ * ( 2 + 2 * Real.log s ) ) ≤ 0 by exact neg_nonpos.mpr ( mul_nonneg ( mul_nonneg ( mul_nonneg zero_le_two hβ.le ) hγ0 ) ( by positivity ) ) ) ]

end