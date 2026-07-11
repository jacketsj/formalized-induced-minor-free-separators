/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-! # Fubini-type helper lemmas for product measures

These lemmas provide tools for bounding the measure of events in product
probability spaces by conditioning on subsets of coordinates.
-/

open MeasureTheory Measure Set

noncomputable section

/-
For a product of two measures, if the conditional measure of a set
is bounded pointwise by a constant, then the product measure is bounded
by that constant.

This is the key Fubini-type inequality used in the padding probability argument.
-/
lemma prod_measure_le_of_slice_bound
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν] [IsProbabilityMeasure μ]
    {E : Set (α × β)} (hE : MeasurableSet E)
    (c : ENNReal)
    (hbound : ∀ x : α, ν (Prod.mk x ⁻¹' E) ≤ c) :
    (μ.prod ν) E ≤ c := by
      -- By Fubini's theorem, we can interchange the order of integration.
      have h_fubini : ∫⁻ x, ν (Prod.mk x ⁻¹' E) ∂μ ≤ c := by
        exact le_trans ( MeasureTheory.lintegral_mono hbound ) ( by simp +decide );
      rwa [ MeasureTheory.Measure.prod_apply hE ]

/-
For a product of two probability measures, the measure of an event depending
on both coordinates can be bounded by integrating the conditional measure.
-/
lemma prod_measure_le_lintegral
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    {E : Set (α × β)} (hE : MeasurableSet E)
    (f : α → ENNReal)
    (hbound : ∀ x : α, ν (Prod.mk x ⁻¹' E) ≤ f x) :
    (μ.prod ν) E ≤ ∫⁻ x, f x ∂μ := by
      convert MeasureTheory.lintegral_mono fun x => hbound x;
      rw [ MeasureTheory.Measure.prod_apply hE ]

/-
For a pi measure on (ι → ℝ), the measure of any event E is bounded
by the supremum of the conditional measures over one coordinate.

Specifically: for predicate p splitting ι, using measurePreserving_piEquivPiSubtypeProd,
the pi measure decomposes as a product, and we can apply prod_measure_le_of_slice_bound.
-/
lemma pi_measure_le_of_coord_slice_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ_each : Measure ℝ) [SigmaFinite μ_each] [IsProbabilityMeasure μ_each]
    (E : Set (ι → ℝ)) (hE : MeasurableSet E)
    (c : ENNReal)
    (i₀ : ι)
    (hbound : ∀ rest : {j : ι // j ≠ i₀} → ℝ,
      μ_each {y : ℝ | (fun j : ι => if h : j = i₀ then y else rest ⟨j, h⟩) ∈ E} ≤ c) :
    (Measure.pi (fun (_ : ι) => μ_each)) E ≤ c := by
      -- Apply the measure-preserving property to rewrite the measure of E in terms of the product measure.
      have h_measure : (Measure.pi (fun _ => μ_each)) E = (Measure.prod (Measure.pi (fun _ : { j // j ≠ i₀ } => μ_each)) μ_each) (Set.preimage (fun (x : ({ j // j ≠ i₀ } → ℝ) × ℝ) => fun j => if h : j = i₀ then x.2 else x.1 ⟨j, h⟩) E) := by
        have h_measure : (Measure.pi (fun _ => μ_each)) = Measure.map (fun (x : ({ j // j ≠ i₀ } → ℝ) × ℝ) => fun j => if h : j = i₀ then x.2 else x.1 ⟨j, h⟩) (Measure.prod (Measure.pi (fun _ : { j // j ≠ i₀ } => μ_each)) μ_each) := by
          refine' MeasureTheory.Measure.pi_eq _;
          intro s hs
          have h_preimage : (fun (x : ({ j // j ≠ i₀ } → ℝ) × ℝ) => fun j => if h : j = i₀ then x.2 else x.1 ⟨j, h⟩) ⁻¹' (Set.pi Set.univ s) = (Set.pi Set.univ (fun (j : { j // j ≠ i₀ }) => s j)) ×ˢ s i₀ := by
            grind;
          rw [ MeasureTheory.Measure.map_apply ];
          · rw [ h_preimage, MeasureTheory.Measure.prod_prod ];
            rw [ show ( ∏ i : ι, μ_each ( s i ) ) = ( ∏ i : { j // j ≠ i₀ }, μ_each ( s i ) ) * μ_each ( s i₀ ) from ?_ ];
            · erw [ MeasureTheory.Measure.pi_pi ];
            · rw [ ← Finset.prod_erase_mul _ _ ( Finset.mem_univ i₀ ), Finset.prod_subtype ] ; aesop;
          · exact measurable_pi_lambda _ fun j => by split_ifs <;> [ exact measurable_snd; exact measurable_pi_apply _ |> Measurable.comp <| measurable_fst ] ;
          · exact MeasurableSet.univ_pi hs;
        rw [ h_measure, Measure.map_apply ];
        · exact measurable_pi_lambda _ fun j => by split_ifs <;> [ exact measurable_snd; exact measurable_pi_apply _ |> Measurable.comp <| measurable_fst ] ;
        · exact hE;
      rw [ h_measure ];
      apply_rules [ prod_measure_le_of_slice_bound ];
      refine' hE.preimage _;
      exact measurable_pi_lambda _ fun _ => by split_ifs <;> [ exact measurable_snd; exact measurable_pi_apply _ |> Measurable.comp <| measurable_fst ] ;

/-
The pi measure of a measurable set `E` equals the integral over the remaining
coordinates of the conditional one-coordinate measure of the slice of `E`.
-/
lemma pi_measure_eq_lintegral_slice
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ_each : Measure ℝ) [SigmaFinite μ_each] [IsProbabilityMeasure μ_each]
    (i₀ : ι) (E : Set (ι → ℝ)) (hE : MeasurableSet E) :
    (Measure.pi (fun _ => μ_each)) E
      = ∫⁻ rest, μ_each {y : ℝ | (fun j => if h : j = i₀ then y else rest ⟨j, h⟩) ∈ E}
          ∂(Measure.pi (fun _ : {j // j ≠ i₀} => μ_each)) := by
  -- We'll use the fact that the measure map `combine` is measure-preserving.
  have h_measure_map : (Measure.pi fun _ => μ_each) = Measure.map (fun (x : ({j : ι // j ≠ i₀} → ℝ) × ℝ) => fun j => if h : j = i₀ then x.2 else x.1 ⟨j, h⟩) (Measure.prod (Measure.pi fun _ => μ_each) μ_each) := by
    refine' MeasureTheory.Measure.pi_eq fun s hs => _;
    rw [ MeasureTheory.Measure.map_apply ];
    · rw [ show ( fun x : ( { j : ι // j ≠ i₀ } → ℝ ) × ℝ => fun j => if h : j = i₀ then x.2 else x.1 ⟨ j, h ⟩ ) ⁻¹' univ.pi s = ( Set.pi Set.univ fun i : { j : ι // j ≠ i₀ } => s i ) ×ˢ s i₀ from ?_ ];
      · rw [ MeasureTheory.Measure.prod_prod ];
        rw [ ← Finset.prod_erase_mul _ _ ( Finset.mem_univ i₀ ), MeasureTheory.Measure.pi_pi ];
        refine' congr_arg₂ _ ( Finset.prod_bij ( fun x _ => x ) _ _ _ _ ) rfl <;> simp +decide;
      · grind +locals;
    · exact measurable_pi_lambda _ fun j => by split_ifs <;> [ exact measurable_snd; exact ( measurable_pi_apply _ ).comp measurable_fst ] ;
    · exact MeasurableSet.univ_pi hs;
  rw [ h_measure_map, Measure.map_apply ] <;> norm_num [ hE ];
  · erw [ MeasureTheory.Measure.prod_apply ];
    · rfl;
    · refine' hE.preimage _;
      exact measurable_pi_lambda _ fun j => by split_ifs <;> [ exact measurable_snd; exact ( measurable_pi_apply _ ).comp measurable_fst ] ;
  · exact measurable_pi_lambda _ fun j => by split_ifs <;> [ exact measurable_snd; exact ( measurable_pi_apply _ ).comp measurable_fst ] ;

/-
If, conditioning on the coordinates other than `i₀`, the one-coordinate measure of
the slice of `EQ` is bounded by `a * (measure of slice of EF + d)`, then the same
bound holds globally for the pi measure.
-/
lemma pi_measure_slice_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ_each : Measure ℝ) [SigmaFinite μ_each] [IsProbabilityMeasure μ_each]
    (i₀ : ι) (EQ EF : Set (ι → ℝ)) (hEQ : MeasurableSet EQ) (hEF : MeasurableSet EF)
    (a d : ENNReal)
    (hslice : ∀ rest : {j // j ≠ i₀} → ℝ,
      μ_each {y : ℝ | (fun j => if h : j = i₀ then y else rest ⟨j, h⟩) ∈ EQ}
        ≤ a * (μ_each {y : ℝ | (fun j => if h : j = i₀ then y else rest ⟨j, h⟩) ∈ EF} + d)) :
    (Measure.pi (fun _ => μ_each)) EQ
      ≤ a * ((Measure.pi (fun _ => μ_each)) EF + d) := by
  rw [ pi_measure_eq_lintegral_slice ];
  refine' le_trans ( MeasureTheory.lintegral_mono fun rest => hslice rest ) _;
  · rw [ MeasureTheory.lintegral_const_mul ];
    · rw [ MeasureTheory.lintegral_add_right' ] <;> norm_num;
      rw [ pi_measure_eq_lintegral_slice ] ; aesop;
    · refine' Measurable.add _ measurable_const;
      convert measurable_measure_prodMk_left ( show MeasurableSet ( { p : ( { j // j ≠ i₀ } → ℝ ) × ℝ | ( fun j => if h : j = i₀ then p.2 else p.1 ⟨ j, h ⟩ ) ∈ EF } ) from ?_ ) using 1;
      · infer_instance;
      · refine' hEF.preimage _;
        exact measurable_pi_lambda _ fun j => by split_ifs <;> [ exact measurable_snd; exact measurable_pi_apply _ |> Measurable.comp <| measurable_fst ] ;
  · exact hEQ

end