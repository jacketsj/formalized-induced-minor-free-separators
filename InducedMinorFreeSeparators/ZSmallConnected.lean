/-
# Z-Small Case: Connected G[S] — Helper Lemmas

When Z is small and G[S] is connected, apply `pure_pairs_fat_model` to G[S]
and convert all three outcomes back to the original graph G.
-/
import Mathlib
import InducedMinorFreeSeparators.ProofDefs
import InducedMinorFreeSeparators.VWSP
import InducedMinorFreeSeparators.CoarsePurePairs
import InducedMinorFreeSeparators.VWSPProperties
import InducedMinorFreeSeparators.ZHandling
import InducedMinorFreeSeparators.ZSmallCase

open Set Function CoarsePurePairs SimpleGraph
open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Parameter condition for the Z-small connected case -/

/-
The rescaled parameter condition for `pure_pairs_fat_model` on G[S].
    When |Z| < 2⌈εn⌉ and n > 32h², we get nS ≥ n - 2⌈εn⌉ + 1,
    which suffices for 2h·(εn/nS) + (h+m-1)·(ηn/nS) < 1.
-/
lemma z_small_param_condition
    (h : ℕ) (hh : 2 ≤ h)
    (n nS : ℕ) (hnS_pos : 0 < nS)
    (hn_large : 32 * (h : ℝ)^2 < n)
    (hnS_lower : (n : ℝ) - 2 * ⌈(13 : ℝ) / (40 * ↑h) * ↑n⌉₊ + 1 ≤ ↑nS) :
    2 * (h : ℝ) * ((13 : ℝ) / (40 * ↑h) * ↑n / ↑nS) +
    ((h : ℝ) + ↑h * (↑h - 1) / 2 - 1) * (1 / (32 * (h : ℝ)^2) * ↑n / ↑nS) < 1 := by
  have h_ceil : (⌈(13 / (40 * h : ℝ)) * n⌉₊ : ℝ) ≤ (13 / (40 * h : ℝ)) * n + 1 := by
    exact le_of_lt <| Nat.ceil_lt_add_one <| by positivity;
  field_simp at *;
  nlinarith [ ( by norm_cast : ( 2 : ℝ ) ≤ h ), pow_two ( h - 2 : ℝ ) ]

omit [Fintype V] [DecidableEq V] in
/-- Z.card > (2ε+η)·n implies 2⌈εn⌉ ≤ Z.card when n > 32h². -/
lemma z_large_implies_split_threshold
    (h : ℕ) (hh : 2 ≤ h)
    (n : ℕ) (hn_large : 32 * (h : ℝ)^2 < n)
    (zcard : ℕ)
    (hZ_large : (2 * (13 : ℝ) / (40 * ↑h) + 1 / (32 * (↑h)^2)) * ↑n < ↑zcard) :
    2 * ⌈(13 : ℝ) / (40 * ↑h) * ↑n⌉₊ ≤ zcard := by
  field_simp at *;
  have := Nat.ceil_lt_add_one ( by positivity : ( 0 : ℝ ) ≤ 13 * n / ( 40 * h ) );
  rw [ div_add_one, lt_div_iff₀ ] at this <;> norm_cast at * <;> nlinarith

omit [Fintype V] [DecidableEq V] in
/-- Convert a fat model from G[S] to an induced minor in G. -/
lemma z_small_fat_model_convert
    (G : SimpleGraph V)
    (h : ℕ)
    (S : Set V)
    (F : HasInducedMinor_internal (G.comap (Subtype.val : S → V))
      (graphOneSubdiv (completeGraph (Fin h)))) :
    HasInducedMinor_internal G (graphOneSubdiv (completeGraph (Fin h))) :=
  hasInducedMinor_internal_of_comap Subtype.val Subtype.val_injective G _ F

end
