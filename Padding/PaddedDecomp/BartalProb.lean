/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Padding.PaddedDecompDefs
import Padding.PaddedDecomp.Bartal
import Padding.PaddedDecomp.BartalHelpers

/-! # Bartal's Theorem with a Universal Padding Constant `δ = Ω(1)`

This file contains the genuine probabilistic proof of Bartal's padded decomposition theorem,
giving a `(O(log n), Ω(1))`-padded decomposition scheme, where the padding parameter
`δ₀ = 1/4` is a **universal constant**, independent of the number of points `n`.

## Construction

We use the standard CKR / Bartal greedy ball-carving construction:

* sample a uniformly random radius `R ~ Uniform[Δ/4, Δ/2]`;
* sample a uniformly random ordering `σ` of the points (a random bijection `Fin n ≃ X`);
* assign each point to the first center (in `σ`-order) within distance `R`
  (this is `greedyBallPart'`).

## Analysis

For a fixed point `z` and padding radius `ρ = γΔ ≤ Δ/4`, conditioned on the radius `R`,
the probability over `σ` that `B(z, ρ)` lands entirely in `z`'s cluster is at least
`|B(z, R-ρ)| / |B(z, R+ρ)|` (this is `greedy_padding_count'`).  Averaging over the uniform
radius `R` and applying Jensen's inequality to the concave `log`,

```
  Pr[B(z, γΔ) ⊆ P(z)]
     ≥ E_R[ |B(z,R-ρ)| / |B(z,R+ρ)| ]
     ≥ exp( E_R[ log|B(z,R-ρ)| - log|B(z,R+ρ)| ] )
     ≥ exp( -8 γ log n ).
```

The last step is a telescoping bound on the integral of the increasing step function
`s ↦ log|B(z,s)|`.  Hence `β = 8 log n` and `δ₀ = 1/4`.
-/

open PaddedDecomposition MeasureTheory Metric Set Real Finset BigOperators ProbabilityTheory

namespace PaddedDecomposition

namespace BartalProb

noncomputable section

open Classical

variable {X : Type u} [MetricSpace X] [Fintype X]

/-- Measurable space on the (finite) space of orderings: the discrete σ-algebra. -/
instance permMeasurable : MeasurableSpace (Fin (Fintype.card X) ≃ X) := ⊤

/-! ## Ball-count step function -/

/-- The number of points within distance `s` of `z` (the cardinality of the closed ball). -/
def bcard (z : X) (s : ℝ) : ℕ :=
  (Finset.univ.filter (fun w : X => dist z w ≤ s)).card

/-- `log` of the ball count: an increasing step function bounded by `log n`. -/
def Hl (z : X) (s : ℝ) : ℝ := Real.log (bcard z s)

/-- The ratio `|B(z, R-ρ)| / |B(z, R+ρ)|`, the per-radius padding lower bound. -/
def brat (z : X) (ρ R : ℝ) : ℝ := (bcard z (R - ρ) : ℝ) / (bcard z (R + ρ) : ℝ)

/-- Radius clamped to `[Δ/4, Δ/2]` (and to `≥ 0`), so that the construction is total. -/
def rclamp (Δ R : ℝ) : ℝ := max 0 (max (Δ / 4) (min R (Δ / 2)))

lemma rclamp_nonneg (Δ R : ℝ) : 0 ≤ rclamp Δ R := le_max_left _ _

lemma rclamp_le (Δ R : ℝ) (hΔ : 0 < Δ) : rclamp Δ R ≤ Δ / 2 := by
  unfold rclamp
  apply max_le (by linarith)
  exact max_le (by linarith) (min_le_right _ _)

lemma rclamp_ge (Δ R : ℝ) : Δ / 4 ≤ rclamp Δ R := by
  unfold rclamp
  exact le_max_of_le_right (le_max_left _ _)

lemma rclamp_eq_self (Δ R : ℝ) (hΔ : 0 < Δ) (h1 : Δ / 4 ≤ R) (h2 : R ≤ Δ / 2) :
    rclamp Δ R = R := by
  unfold rclamp
  rw [min_eq_left h2, max_eq_right h1, max_eq_right (by linarith)]

/-! ## Basic facts about `bcard` and `Hl` -/

lemma bcard_pos (z : X) {s : ℝ} (hs : 0 ≤ s) : 0 < bcard z s := by
  apply Finset.card_pos.mpr
  exact ⟨z, by simp [hs]⟩

lemma bcard_le (z : X) (s : ℝ) : bcard z s ≤ Fintype.card X := by
  simpa [bcard] using Finset.card_filter_le _ _

lemma bcard_mono (z : X) : Monotone (bcard z) := by
  intro a b hab
  apply Finset.card_le_card
  intro w hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
  linarith

lemma Hl_nonneg (z : X) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ Hl z s := by
  apply Real.log_nonneg
  exact_mod_cast bcard_pos z hs

lemma Hl_le (z : X) (s : ℝ) : Hl z s ≤ Real.log (Fintype.card X) := by
  unfold Hl
  have hcard : 1 ≤ Fintype.card X := Fintype.card_pos_iff.mpr ⟨z⟩
  rcases Nat.eq_zero_or_pos (bcard z s) with h | h
  · rw [h, Nat.cast_zero, Real.log_zero]
    exact Real.log_nonneg (by exact_mod_cast hcard)
  · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast bcard_le z s)

lemma Hl_mono (z : X) : Monotone (Hl z) := by
  intro a b hab
  unfold Hl
  rcases Nat.eq_zero_or_pos (bcard z a) with h | h
  · rw [h, Nat.cast_zero, Real.log_zero]
    rcases Nat.eq_zero_or_pos (bcard z b) with h2 | h2
    · rw [h2, Nat.cast_zero, Real.log_zero]
    · exact Real.log_nonneg (by exact_mod_cast h2)
  · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast bcard_mono z hab)

lemma Hl_measurable (z : X) : Measurable (Hl z) := (Hl_mono z).measurable

/-! ## The two probability measures -/

/-- The uniform measure on orderings of `X`. -/
def νp (X : Type u) [MetricSpace X] [Fintype X] : Measure (Fin (Fintype.card X) ≃ X) :=
  uniformOn Set.univ

/-- The uniform radius measure on `[Δ/4, Δ/2]` (a probability measure when `Δ > 0`). -/
def νR (Δ : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (4 / Δ)) • volume.restrict (Set.Icc (Δ / 4) (Δ / 2))

instance νp_isProbabilityMeasure : IsProbabilityMeasure (νp X) := by
  unfold νp
  haveI : Nonempty (Fin (Fintype.card X) ≃ X) := ⟨Fintype.equivOfCardEq (by simp)⟩
  exact isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty

instance νR_isProbabilityMeasure (Δ : ℝ) (hΔ : 0 < Δ) : IsProbabilityMeasure (νR Δ) := by
  constructor;
  unfold νR; simp +decide ;
  rw [ ← ENNReal.ofReal_mul ( by positivity ) ] ; ring_nf ; norm_num [ hΔ.ne' ]

/-! ## The random partition -/

/-- The random partition: given a radius `R` and an ordering `σ`, the greedy ball partition
with the clamped radius. -/
def bpart (Δ : ℝ) (ω : ℝ × (Fin (Fintype.card X) ≃ X)) : Partition X :=
  greedyBallPart' ω.2 (rclamp Δ ω.1) (rclamp_nonneg Δ ω.1)

lemma bpart_isBounded (Δ : ℝ) (hΔ : 0 < Δ) (ω : ℝ × (Fin (Fintype.card X) ≃ X)) :
    (bpart Δ ω).IsBounded Δ := by
  apply greedyBallPart'_isBounded
  have := rclamp_le Δ ω.1 hΔ
  linarith

/-! ## Per-radius padding lower bound -/

/-
For a fixed radius `R`, the probability over orderings that `B(z, ρ)` is padded is at least
the ratio `brat`.
-/
lemma νp_section_ge (Δ : ℝ) (hΔ : 0 < Δ) (_hn : 2 ≤ Fintype.card X)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Δ / 4) (z : X) (R : ℝ) :
    (νp X) {σ : Fin (Fintype.card X) ≃ X |
        Metric.closedBall z ρ ⊆ (greedyBallPart' σ (rclamp Δ R) (rclamp_nonneg Δ R)).cluster z}
      ≥ ENNReal.ofReal (brat z ρ (rclamp Δ R)) := by
  generalize_proofs at *;
  unfold νp;
  rw [ uniformOn ];
  rw [ ProbabilityTheory.cond_apply ];
  · simp +decide [ Measure.count_apply ];
    rw [ ENNReal.ofReal_le_iff_le_toReal ];
    · rw [ Set.encard_eq_coe_toFinset_card ] ; norm_num [ brat ];
      rw [ inv_mul_eq_div, div_le_div_iff₀ ] <;> norm_cast;
      · convert greedy_padding_count' ( rclamp Δ R ) ρ _ _ _ z using 1;
        · exact lt_max_of_lt_right ( lt_max_of_lt_left ( by positivity ) );
        · linarith;
        · exact le_trans hρ ( rclamp_ge Δ R );
      · exact bcard_pos z ( by have := rclamp_nonneg Δ R; linarith );
      · exact Fintype.card_pos_iff.mpr ⟨ Fintype.equivOfCardEq ( by simp +decide ) ⟩;
    · simp +decide [ ENNReal.mul_eq_top ];
      exact ⟨ Set.toFinite _, fun h => absurd h <| ne_of_gt <| Fintype.card_pos_iff.mpr ⟨ Fintype.equivOfCardEq <| by simp +decide ⟩ ⟩;
  · exact MeasurableSet.univ

/-! ## Measurability of the padding event -/

lemma rclamp_continuous (Δ : ℝ) : Continuous (rclamp Δ) := by
  unfold rclamp; fun_prop

/-
For a fixed ordering `σ` and point `w`, the label as a function of the radius is measurable
(it is a step function: it changes only at the finitely many distances `dist w (σ i)`).
-/
lemma label_measurable (Δ : ℝ) (σ : Fin (Fintype.card X) ≃ X) (w : X) :
    Measurable (fun R => (bpart Δ (R, σ)).label w) := by
  unfold bpart;
  refine' measurable_of_Iic _;
  intro x
  simp [greedyBallPart'];
  refine' MeasurableSet.preimage _ _;
  exact Nat.instMeasurableSpace;
  · exact measurableSet_Iic;
  · refine' Measurable.comp ( show Measurable ( fun x : Fin ( Fintype.card X ) => ( x : ℕ ) ) from by measurability ) _;
    refine' measurable_of_Iic _;
    intro i;
    simp +decide [ Finset.min', Set.preimage ];
    refine' Measurable.exists _;
    intro j;
    exact Measurable.and ( measurableSet_le measurable_const ( rclamp_continuous Δ |> Continuous.measurable ) |> MeasurableSet.mem ) measurable_const

/-
For a fixed ordering `σ`, the set of radii for which a fixed set `S` is contained in
the cluster of `z` is measurable.
-/
lemma cluster_subset_event_section_measurable (Δ : ℝ) (S : Set X) (z : X)
    (σ : Fin (Fintype.card X) ≃ X) :
    MeasurableSet {R : ℝ |
      S ⊆ (bpart Δ (R, σ)).cluster z} := by
  simp +decide [ Set.subset_def, Partition.mem_cluster_iff ];
  refine' Measurable.forall fun x => Measurable.imp _ _;
  · exact measurable_const;
  · exact MeasurableSet.mem ( measurableSet_eq_fun ( label_measurable Δ σ x ) ( label_measurable Δ σ z ) )

/-
The event that a fixed set `S` is contained in the cluster of `z` is measurable in the
product σ-algebra.
-/
lemma cluster_subset_event_measurable (Δ : ℝ) (S : Set X) (z : X) :
    MeasurableSet {ω : ℝ × (Fin (Fintype.card X) ≃ X) |
      S ⊆ (bpart Δ ω).cluster z} := by
  refine' MeasurableSet.congr _ _;
  exact Set.iUnion fun σ : Fin ( Fintype.card X ) ≃ X => { R : ℝ | S ⊆ ( bpart Δ ( R, σ ) ).cluster z } ×ˢ { σ };
  · convert MeasurableSet.iUnion _;
    · infer_instance;
    · intro σ; exact MeasurableSet.prod ( cluster_subset_event_section_measurable Δ S z σ ) ( MeasurableSet.of_discrete ) ;
  · ext ⟨R, σ⟩; simp [Set.mem_iUnion]

/-- The padding event is measurable in the product σ-algebra. -/
lemma event_measurable (Δ : ℝ) (ρ : ℝ) (z : X) :
    MeasurableSet {ω : ℝ × (Fin (Fintype.card X) ≃ X) |
      Metric.closedBall z ρ ⊆ (bpart Δ ω).cluster z} :=
  cluster_subset_event_measurable Δ (Metric.closedBall z ρ) z

/-! ## The telescoping integral bound -/

/-
The core telescoping bound:
`∫_{Δ/4}^{Δ/2} (Hl(R-ρ) - Hl(R+ρ)) dR ≥ -2 ρ log n`.
-/
lemma Hl_interval_integral_ge (Δ : ℝ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Δ / 4)
    (z : X) :
    (∫ R in (Δ / 4)..(Δ / 2), (Hl z (R - ρ) - Hl z (R + ρ)))
      ≥ -(2 * ρ * Real.log (Fintype.card X)) := by
  rw [ intervalIntegral.integral_sub ] <;> norm_num;
  · rw [ show Δ / 2 + ρ = ( Δ / 4 + ρ ) + ( Δ / 4 ) by ring, show Δ / 2 - ρ = ( Δ / 4 - ρ ) + ( Δ / 4 ) by ring ];
    rw [ show ( ∫ x in Δ / 4 + ρ..Δ / 4 + ρ + Δ / 4, Hl z x ) = ( ∫ x in Δ / 4 + ρ..Δ / 4 - ρ + Δ / 4, Hl z x ) + ( ∫ x in Δ / 4 - ρ + Δ / 4..Δ / 4 + ρ + Δ / 4, Hl z x ) from ?_, show ( ∫ x in Δ / 4 - ρ..Δ / 4 - ρ + Δ / 4, Hl z x ) = ( ∫ x in Δ / 4 - ρ..Δ / 4 + ρ, Hl z x ) + ( ∫ x in Δ / 4 + ρ..Δ / 4 - ρ + Δ / 4, Hl z x ) from ?_ ];
    · -- The integral of a non-negative function over an interval is non-negative.
      have h_nonneg : 0 ≤ ∫ x in Δ / 4 - ρ..Δ / 4 + ρ, Hl z x := by
        refine' intervalIntegral.integral_nonneg _ _ <;> norm_num;
        · linarith;
        · exact fun u hu₁ hu₂ => Hl_nonneg z ( by linarith );
      have h_bound : ∫ x in Δ / 4 - ρ + Δ / 4..Δ / 4 + ρ + Δ / 4, Hl z x ≤ ∫ x in Δ / 4 - ρ + Δ / 4..Δ / 4 + ρ + Δ / 4, Real.log (Fintype.card X) := by
        apply_rules [ intervalIntegral.integral_mono_on ];
        · linarith;
        · apply_rules [ Monotone.intervalIntegrable, Hl_mono ];
        · norm_num;
        · exact fun x hx => Hl_le z x;
      norm_num at * ; linarith;
    · rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ Monotone.intervalIntegrable, Hl_mono ];
    · rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ Monotone.intervalIntegrable, Hl_mono ];
  · apply_rules [ Monotone.intervalIntegrable ];
    exact fun x y hxy => Hl_mono z ( by linarith );
  · apply_rules [ Monotone.intervalIntegrable ];
    exact fun x y hxy => Hl_mono z ( by linarith )

/-! ## Integrability -/

lemma brat_integrable (Δ : ℝ) (hΔ : 0 < Δ) (ρ : ℝ) (z : X) :
    Integrable (fun R => brat z ρ R) (νR Δ) := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun R => Fintype.card X;
  · simp +decide [ νR ];
    rw [ MeasureTheory.integrable_smul_measure ] <;> norm_num;
    exact hΔ;
  · refine' Measurable.aestronglyMeasurable _;
    refine' Measurable.mul _ _;
    · exact Measurable.comp ( by measurability ) ( show Measurable ( fun R => bcard z ( R - ρ ) ) from by simpa using ( bcard_mono z |> Monotone.measurable |> Measurable.comp <| measurable_id.sub_const ρ ) );
    · exact Measurable.inv ( Measurable.comp ( by measurability ) ( bcard_mono z |> Monotone.measurable |> Measurable.comp <| measurable_id.add_const ρ ) );
  · refine' Filter.Eventually.of_forall fun R => _;
    unfold brat;
    by_cases h : bcard z ( R + ρ ) = 0 <;> simp_all +decide;
    exact le_trans ( div_le_self ( Nat.cast_nonneg _ ) ( mod_cast Nat.one_le_iff_ne_zero.mpr h ) ) ( mod_cast bcard_le z _ )

lemma logbrat_integrable (Δ : ℝ) (hΔ : 0 < Δ) (ρ : ℝ) (z : X) :
    Integrable (fun R => Hl z (R - ρ) - Hl z (R + ρ)) (νR Δ) := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun R => Real.log ( Fintype.card X );
  · simp +decide [ νR ];
    rw [ MeasureTheory.integrable_smul_measure ] <;> norm_num;
    exact hΔ;
  · exact Measurable.aestronglyMeasurable ( by exact Measurable.sub ( Hl_measurable z |> Measurable.comp <| measurable_id.sub_const _ ) ( Hl_measurable z |> Measurable.comp <| measurable_id.add_const _ ) );
  · refine' Filter.Eventually.of_forall fun R => _;
    refine' abs_sub_le_iff.mpr ⟨ _, _ ⟩;
    · refine' le_trans ( sub_le_self _ ( _ ) ) _;
      · exact Real.log_natCast_nonneg _;
      · exact Hl_le z _;
    · refine' le_trans ( sub_le_self _ <| _ ) _;
      · exact Real.log_natCast_nonneg _;
      · exact Hl_le z _

/-! ## The radius-averaged padding bound -/

/-
The `νR`-integral of the log-ratio equals `(4/Δ)` times the interval integral, hence is
bounded below by `-(8 γ log n)` via the telescoping bound.
-/
lemma logbrat_nu_integral_ge (Δ : ℝ) (hΔ : 0 < Δ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγδ : γ ≤ 1 / 4)
    (z : X) :
    (∫ R, (Hl z (R - γ * Δ) - Hl z (R + γ * Δ)) ∂(νR Δ))
      ≥ -(8 * γ * Real.log (Fintype.card X)) := by
  rw [ show νR Δ = ( ENNReal.ofReal ( 4 / Δ ) ) • MeasureTheory.Measure.restrict MeasureTheory.volume ( Set.Icc ( Δ / 4 ) ( Δ / 2 ) ) from rfl, MeasureTheory.integral_smul_measure ] ; norm_num [ hΔ.ne' ];
  rw [ ENNReal.toReal_ofReal ( by positivity ), MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ] <;> try linarith;
  have := Hl_interval_integral_ge Δ ( γ * Δ ) ( by positivity ) ( by nlinarith ) z;
  rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> nlinarith

/-
`exp` of the log-ratio is integrable w.r.t. `νR`.
-/
lemma expf_integrable (Δ : ℝ) (hΔ : 0 < Δ) (ρ : ℝ) (z : X) :
    Integrable (fun R => Real.exp (Hl z (R - ρ) - Hl z (R + ρ))) (νR Δ) := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun R => Real.exp ( Real.log ( Fintype.card X ) );
  · convert MeasureTheory.integrable_const ( Real.exp ( Real.log ( Fintype.card X ) ) );
    constructor;
    convert MeasureTheory.IsProbabilityMeasure.measure_univ.trans_lt ENNReal.one_lt_top using 1;
    exact νR_isProbabilityMeasure Δ hΔ;
  · exact Measurable.aestronglyMeasurable ( by exact Measurable.exp ( by exact Measurable.sub ( Hl_measurable z |> Measurable.comp <| measurable_id.sub_const _ ) ( Hl_measurable z |> Measurable.comp <| measurable_id.add_const _ ) ) );
  · simp +zetaDelta at *;
    refine' Filter.Eventually.of_forall fun R => le_add_of_le_of_nonneg _ _;
    · exact Hl_le z _;
    · exact Real.log_natCast_nonneg _

/-
On the support `[Δ/4, Δ/2]` of `νR`, `exp` of the log-ratio equals the ratio `brat`.
-/
lemma expf_eq_brat_ae (Δ : ℝ) (hΔ : 0 < Δ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγδ : γ ≤ 1 / 4)
    (z : X) :
    (fun R => Real.exp (Hl z (R - γ * Δ) - Hl z (R + γ * Δ)))
      =ᵐ[νR Δ] (fun R => brat z (γ * Δ) R) := by
  refine' Filter.eventuallyEq_of_mem _ _;
  exact Set.Icc ( Δ / 4 ) ( Δ / 2 );
  · unfold νR;
    simp +decide [ MeasureTheory.mem_ae_iff ];
  · intro R hR; simp +decide [ Hl, brat ] ;
    rw [ Real.exp_sub, Real.exp_log ( Nat.cast_pos.mpr <| bcard_pos z <| by nlinarith [ hR.1, hR.2 ] ), Real.exp_log ( Nat.cast_pos.mpr <| bcard_pos z <| by nlinarith [ hR.1, hR.2 ] ) ]

/-- The expectation of the ratio over the uniform radius is at least `exp(-8 γ log n)`. -/
lemma brat_integral_ge (Δ : ℝ) (hΔ : 0 < Δ)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγδ : γ ≤ 1 / 4) (z : X) :
    (∫ R, brat z (γ * Δ) R ∂(νR Δ))
      ≥ Real.exp (-(8 * Real.log (Fintype.card X)) * γ) := by
  haveI := νR_isProbabilityMeasure Δ hΔ
  -- rewrite ∫ brat = ∫ exp(logratio) using the a.e. equality
  rw [← MeasureTheory.integral_congr_ae (expf_eq_brat_ae Δ hΔ γ hγ0 hγδ z)]
  -- Jensen: exp(∫ f) ≤ ∫ exp(f)
  have hjensen : Real.exp (∫ R, (Hl z (R - γ * Δ) - Hl z (R + γ * Δ)) ∂(νR Δ))
      ≤ ∫ R, Real.exp (Hl z (R - γ * Δ) - Hl z (R + γ * Δ)) ∂(νR Δ) := by
    have := convexOn_exp.map_integral_le (μ := νR Δ)
      (f := fun R => Hl z (R - γ * Δ) - Hl z (R + γ * Δ))
      (continuousOn_exp) isClosed_univ (by filter_upwards with x using Set.mem_univ _)
      (logbrat_integrable Δ hΔ (γ * Δ) z) (expf_integrable Δ hΔ (γ * Δ) z)
    simpa using this
  refine le_trans ?_ hjensen
  -- exp is monotone, and ∫ f ≥ -8γ log n
  apply Real.exp_le_exp.mpr
  have := logbrat_nu_integral_ge Δ hΔ γ hγ0 hγδ z
  nlinarith [this]

/-! ## The key padding inequality -/

lemma padding_key (hn : 2 ≤ Fintype.card X) (Δ : ℝ) (hΔ : 0 < Δ)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγδ : γ ≤ 1 / 4) (z : X) :
    ((νR Δ).prod (νp X)).toOuterMeasure
        {ω : ℝ × (Fin (Fintype.card X) ≃ X) |
          Metric.closedBall z (γ * Δ) ⊆ (bpart Δ ω).cluster z}
      ≥ ENNReal.ofReal (Real.exp (-(8 * Real.log (Fintype.card X)) * γ)) := by
  -- Apply the provided lemma `brat_integral_ge` to conclude the proof.
  have := brat_integral_ge Δ hΔ γ hγ0 hγδ z;
  simp_all +decide [ νR ];
  rw [ MeasureTheory.Measure.prod_apply ];
  · refine' le_trans _ ( MeasureTheory.lintegral_mono_ae _ );
    rotate_left;
    use fun R => ENNReal.ofReal ( brat z ( γ * Δ ) R );
    · rw [ MeasureTheory.ae_iff ] ; norm_num;
      refine' Or.inr ( MeasureTheory.measure_mono_null _ ( MeasureTheory.measure_empty ) );
      intro R hR; contrapose! hR; simp_all +decide [ bpart ] ;
      intro h₁ h₂; contrapose! h₁; exact (by
      convert νp_section_ge Δ hΔ hn ( γ * Δ ) ( by positivity ) ( by nlinarith ) z R |> le_trans _ using 1;
      rw [ rclamp_eq_self Δ R hΔ h₂ h₁ ]);
    · rw [ MeasureTheory.lintegral_smul_measure ];
      rw [ ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
      · convert ENNReal.ofReal_le_ofReal this using 1;
        rw [ ENNReal.ofReal_mul ( by positivity ), ENNReal.ofReal_toReal ( by simp +decide ) ];
        rfl;
      · contrapose! this;
        rw [ MeasureTheory.integral_undef this ] ; norm_num [ hΔ.ne' ] ; positivity;
      · exact Filter.Eventually.of_forall fun x => div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ );
  · exact event_measurable Δ (γ * Δ) z

/-! ## Assembling the padded decomposition -/

/-- The `(8 log n, 1/4, Δ)`-padded decomposition for an `n ≥ 2` point metric space. -/
def bartalDecomp (hn : 2 ≤ Fintype.card X) (Δ : ℝ) (hΔ : 0 < Δ) :
    PaddedDecomp X (8 * Real.log (Fintype.card X)) (1 / 4) Δ where
  Ω := ℝ × (Fin (Fintype.card X) ≃ X)
  msΩ := by infer_instance
  μ := (νR Δ).prod (νp X)
  hμ := by
    haveI := νR_isProbabilityMeasure Δ hΔ
    infer_instance
  partition := bpart Δ
  bounded := fun ω => bpart_isBounded Δ hΔ ω
  cluster_subset_measurable := cluster_subset_event_measurable Δ
  padding := fun γ hγ0 hγδ z => by
    have h := padding_key hn Δ hΔ γ hγ0 hγδ z
    simpa using h

end

end BartalProb

/-! ## Bartal's Theorem (strong form, `δ = Ω(1)`) -/

/-- **Bartal's Theorem** (strong form): every finite metric space admits an
`(8 log n, 1/4)`-padded decomposition scheme.  Crucially, the padding parameter `δ₀ = 1/4`
is a **universal constant**, independent of the number of points. -/
theorem bartal_padded_decomposition_strong (X : Type u) [MetricSpace X] [Fintype X] :
    AdmitsPaddedDecompScheme X (8 * Real.log (Fintype.card X)) (1 / 4) := by
  by_cases hn : 2 ≤ Fintype.card X
  · intro Δ hΔ
    exact ⟨BartalProb.bartalDecomp hn Δ hΔ⟩
  · -- n ≤ 1: subsingleton space
    push_neg at hn
    have hsub : Subsingleton X := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    have hlog : Real.log (Fintype.card X : ℝ) = 0 := by
      interval_cases h : (Fintype.card X) <;> simp
    rw [hlog, mul_zero]
    have := admitsScheme_subsingleton X (1 / 4)
    simpa using this

end PaddedDecomposition
