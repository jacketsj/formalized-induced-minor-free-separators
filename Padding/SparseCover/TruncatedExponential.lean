/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-! # Truncated Exponential Distribution

The `[0,1]`-truncated exponential distribution with parameter `λ > 0` has density
`g(y) = λ · e^{-λy} / (1 - e^{-λ})` for `y ∈ [0,1]`.

We define this measure and prove key properties needed for the sparse cover →
padded decomposition proof.
-/

open MeasureTheory Measure Set Real

noncomputable section

/-- The density of the truncated exponential distribution on `[0,1]` with parameter `l`. -/
def texpDensityReal (l : ℝ) (y : ℝ) : ℝ :=
  l * Real.exp (-l * y) / (1 - Real.exp (-l))

/-- The density as an ENNReal-valued function. -/
def texpDensity (l : ℝ) : ℝ → ENNReal :=
  fun y => ENNReal.ofReal (texpDensityReal l y)

/-- The truncated exponential measure on `ℝ` with parameter `l > 0`, supported on `[0,1]`.
    This is `volume.restrict(Icc 0 1)` weighted by the density
    `λ · e^{-λy} / (1 - e^{-λ})`. -/
def texpMeasure (l : ℝ) : Measure ℝ :=
  (volume.restrict (Icc 0 1)).withDensity (texpDensity l)

/-- The density is non-negative for `l > 0`. -/
lemma texpDensityReal_nonneg {l : ℝ} (hl : 0 < l) (y : ℝ) :
    0 ≤ texpDensityReal l y := by
  unfold texpDensityReal
  apply div_nonneg
  · exact mul_nonneg hl.le (exp_nonneg _)
  · have : Real.exp (-l) < 1 := by rw [exp_lt_one_iff]; linarith
    linarith

/-
The total integral of the density over `[0,1]` equals 1 when `l > 0`.
-/
lemma texpMeasure_univ {l : ℝ} (hl : 0 < l) :
    texpMeasure l Set.univ = 1 := by
      unfold texpMeasure texpDensity;
      simp +decide [ texpDensityReal ];
      rw [ ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
      · rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ] <;> norm_num;
        rw [ intervalIntegral.integral_comp_mul_left ( fun x => Real.exp ( -x ) ) ] <;> norm_num [ hl.ne' ];
        exact ne_of_gt ( by norm_num; positivity );
      · exact Continuous.integrableOn_Icc ( by continuity );
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with y hy using div_nonneg ( mul_nonneg hl.le ( Real.exp_nonneg _ ) ) ( sub_nonneg.2 ( Real.exp_le_one_iff.2 ( by linarith ) ) )

/-- The truncated exponential measure is a probability measure for `l > 0`. -/
lemma texpMeasure_isProbabilityMeasure {l : ℝ} (hl : 0 < l) :
    IsProbabilityMeasure (texpMeasure l) where
  measure_univ := texpMeasure_univ hl

/-- The truncated exponential measure is sigma-finite. -/
lemma texpMeasure_sigmaFinite {l : ℝ} (hl : 0 < l) :
    SigmaFinite (texpMeasure l) := by
  haveI := texpMeasure_isProbabilityMeasure hl
  exact inferInstance

/-- The CDF of the truncated exponential: `Pr[δ ≤ x]` for `x ∈ [0,1]`. -/
def texpCDF (l x : ℝ) : ℝ :=
  (1 - Real.exp (-l * x)) / (1 - Real.exp (-l))

/-- The survival function: `Pr[δ > x]` for `x ∈ [0,1]`. -/
def texpSurvivalFn (l x : ℝ) : ℝ :=
  (Real.exp (-l * x) - Real.exp (-l)) / (1 - Real.exp (-l))

lemma texpCDF_add_survival (l x : ℝ) (hl : 0 < l) :
    texpCDF l x + texpSurvivalFn l x = 1 := by
  unfold texpCDF texpSurvivalFn
  have hden : (1 - Real.exp (-l)) ≠ 0 := by
    have : Real.exp (-l) < 1 := by rw [exp_lt_one_iff]; linarith
    linarith
  field_simp
  ring

/-
The measure of `(a, 1]` under the truncated exponential equals the survival function.
-/
lemma texpMeasure_Ioc {l a : ℝ} (hl : 0 < l) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    texpMeasure l (Ioc a 1) = ENNReal.ofReal (texpSurvivalFn l a) := by
      have h_integral : ∫ y in Set.Ioc a 1, l * Real.exp (-l * y) / (1 - Real.exp (-l)) = (Real.exp (-l * a) - Real.exp (-l)) / (1 - Real.exp (-l)) := by
        rw [ ← intervalIntegral.integral_of_le ha1, intervalIntegral.integral_div, intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left ] <;> norm_num [ hl.ne' ];
      convert congr_arg ENNReal.ofReal h_integral using 1;
      rw [ MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
      · convert MeasureTheory.withDensity_apply _ _ using 1;
        · rw [ MeasureTheory.Measure.restrict_restrict_of_subset ( Set.Ioc_subset_Icc_self.trans ( Set.Icc_subset_Icc ha le_rfl ) ) ] ; rfl;
        · norm_num;
      · exact Continuous.integrableOn_Ioc ( by continuity );
      · exact Filter.Eventually.of_forall fun x => div_nonneg ( mul_nonneg hl.le ( Real.exp_nonneg _ ) ) ( sub_nonneg.2 ( Real.exp_le_one_iff.2 ( by linarith ) ) )

/-
The measure of `[a, b]` under the truncated exponential.
-/
lemma texpMeasure_Icc_eq {l a b : ℝ} (hl : 0 < l) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    texpMeasure l (Icc a b) =
    ENNReal.ofReal ((Real.exp (-l * a) - Real.exp (-l * b)) / (1 - Real.exp (-l))) := by
      convert congr_arg ENNReal.ofReal ( show ∫ x in a..b, Real.exp ( -l * x ) * ( l / ( 1 - Real.exp ( -l ) ) ) = ( Real.exp ( -l * a ) - Real.exp ( -l * b ) ) / ( 1 - Real.exp ( -l ) ) from ?_ ) using 1;
      · rw [ intervalIntegral.integral_of_le hab, MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
        · rw [ MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc ];
          rw [ texpMeasure, MeasureTheory.withDensity_apply' ];
          rw [ MeasureTheory.Measure.restrict_restrict_of_subset ( Set.Icc_subset_Icc ha hb ) ] ; congr ; ext ; unfold texpDensity ; ring_nf;
          unfold texpDensityReal; ring_nf;
        · exact Continuous.integrableOn_Ioc ( by continuity );
        · exact Filter.Eventually.of_forall fun x => mul_nonneg ( Real.exp_nonneg _ ) ( div_nonneg hl.le ( sub_nonneg.2 ( Real.exp_le_one_iff.2 ( by linarith ) ) ) );
      · rw [ intervalIntegral.integral_mul_const, intervalIntegral.integral_comp_mul_left ] <;> norm_num <;> ring_nf ; norm_num [ hl.ne' ];
        positivity

/-
The measure of `(a, b]` under the truncated exponential.
-/
lemma texpMeasure_Ioc_eq {l a b : ℝ} (hl : 0 < l) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    texpMeasure l (Ioc a b) =
    ENNReal.ofReal ((Real.exp (-l * a) - Real.exp (-l * b)) / (1 - Real.exp (-l))) := by
      rw [ texpMeasure, MeasureTheory.withDensity_apply' ];
      -- The integral of the density function over the interval (a, b] is equal to the difference of the CDF evaluated at b and a.
      have h_integral : ∫⁻ (a : ℝ) in Ioc a b, texpDensity l a ∂volume.restrict (Icc 0 1) = ENNReal.ofReal (∫ x in a..b, (l * Real.exp (-l * x)) / (1 - Real.exp (-l))) := by
        rw [ intervalIntegral.integral_of_le hab, MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
        · rw [ MeasureTheory.Measure.restrict_restrict_of_subset ( Set.Ioc_subset_Icc_self.trans ( Set.Icc_subset_Icc ( by linarith ) ( by linarith ) ) ) ];
          rfl;
        · exact Continuous.integrableOn_Ioc ( by continuity );
        · exact Filter.Eventually.of_forall fun x => div_nonneg ( mul_nonneg hl.le ( Real.exp_nonneg _ ) ) ( sub_nonneg.2 ( Real.exp_le_one_iff.2 ( by linarith ) ) );
      rw [ h_integral, intervalIntegral.integral_div, intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left ] <;> norm_num [ hl.ne' ]

end