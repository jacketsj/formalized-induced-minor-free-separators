/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.PaddedDecompDefs

/-! # Proof of Bartal's Padded Decomposition Theorem

This file contains the **proof** of `bartal_padded_decomposition` using a
deterministic connected-component partition.

For the definitions, see `Padding/PaddedDecompDefs.lean`.
The strong form with a universal padding constant `δ₀ = 1/4`
(`bartal_padded_decomposition_strong`) is proved in `BartalProb.lean`.
-/

open PaddedDecomposition MeasureTheory Metric Set Real

namespace PaddedDecomposition

noncomputable section

open Classical

/-! ## Connected Component Partition -/

variable {X : Type*}

/-- The connected component partition with threshold `r`. -/
def componentPart [PseudoMetricSpace X] [Fintype X] (r : ℝ) : Partition X where
  label x :=
    let e := Fintype.equivFin X
    (Finset.univ.filter (fun i : Fin (Fintype.card X) =>
      Relation.ReflTransGen (fun a b => dist a b ≤ r) x (e.symm i))).min'
      (by simp only [Finset.filter_nonempty_iff]
          exact ⟨e x, Finset.mem_univ _, by simp [Relation.ReflTransGen.refl]⟩)

/-
Points within distance `r` get the same component label.
-/
lemma componentPart_label_eq_of_dist_le [PseudoMetricSpace X] [Fintype X]
    {r : ℝ} {x y : X} (h : dist x y ≤ r) :
    (componentPart (X := X) r).label x = (componentPart (X := X) r).label y := by
  refine' le_antisymm _ _ <;> simp +decide [ componentPart, Finset.min' ];
  · intro b hb;
    exact ⟨ b, Relation.ReflTransGen.head h hb, le_rfl ⟩;
  · intro b hb; use b; simp_all +decide ;
    exact hb.head ( by simpa [ dist_comm ] using h )

/-- The closed ball of radius `r` is contained in the cluster. -/
lemma componentPart_closedBall_subset [PseudoMetricSpace X] [Fintype X]
    (r : ℝ) (z : X) :
    Metric.closedBall z r ⊆ (componentPart (X := X) r).cluster z := by
  intro w hw
  rw [Partition.mem_cluster_iff]
  exact componentPart_label_eq_of_dist_le (mem_closedBall.mp hw)

/-
Chain distance bound: connected points in a finite space have bounded distance.
-/
lemma reflTransGen_dist_le [PseudoMetricSpace X] [Fintype X]
    {r : ℝ} (hr : 0 ≤ r) {x y : X}
    (h : Relation.ReflTransGen (fun a b => dist a b ≤ r) x y) :
    dist x y ≤ (Fintype.card X - 1 : ℝ) * r := by
  -- Construct a graph G where vertices are points in X, and there is an edge between a and b if dist a b ≤ r.
  set G : SimpleGraph X := SimpleGraph.fromRel (fun a b => dist a b ≤ r);
  obtain ⟨p, hp⟩ : ∃ p : G.Walk x y, p.IsPath := by
    have h_walk : ∃ p : G.Walk x y, True := by
      induction h;
      · exact ⟨ SimpleGraph.Walk.nil, trivial ⟩;
      · rename_i b c h₁ h₂ h₃;
        obtain ⟨ p, hp ⟩ := h₃;
        by_cases h : b = c <;> simp_all +decide;
        · exact ⟨ h ▸ p ⟩;
        · exact ⟨ p.append ( SimpleGraph.Walk.cons ( by aesop ) SimpleGraph.Walk.nil ) ⟩;
    exact ⟨ h_walk.choose.toPath, h_walk.choose.toPath.isPath ⟩;
  have h_path_length : p.length ≤ Fintype.card X - 1 := by
    have := hp.support_nodup.length_le_card;
    grind;
  have h_dist_le_path_length : dist x y ≤ p.length * r := by
    have h_dist_le_path_length : ∀ (u v : X) (p : G.Walk u v), p.IsPath → dist u v ≤ p.length * r := by
      intro u v p hp; induction' p with u v p ih <;> simp_all +decide ;
      cases ‹¬v = p ∧ ( dist v p ≤ r ∨ dist p v ≤ r ) ›.2 <;> linarith [ dist_triangle v p ih, dist_comm v p ];
    exact h_dist_le_path_length x y p hp;
  exact h_dist_le_path_length.trans ( mul_le_mul_of_nonneg_right ( le_trans ( Nat.cast_le.mpr h_path_length ) ( by rw [ Nat.cast_pred ( Fintype.card_pos_iff.mpr ⟨ x ⟩ ) ] ) ) hr )

/-
The connected component partition is Δ-bounded.
-/
lemma componentPart_isBounded [PseudoMetricSpace X] [Fintype X]
    (r : ℝ) (Δ : ℝ) (hr : 0 ≤ r) (hΔ : (Fintype.card X - 1 : ℝ) * r ≤ Δ) :
    (componentPart (X := X) r).IsBounded Δ := by
  intro z
  have h_cluster : ∀ x y, x ∈ (componentPart r).cluster z → y ∈ (componentPart r).cluster z → dist x y ≤ (Fintype.card X - 1 : ℝ) * r := by
    -- Since x and y are in the same connected component, there exists a sequence of points connecting them with each step of distance at most r.
    have h_seq : ∀ x y : X, (componentPart r).label x = (componentPart r).label y → Relation.ReflTransGen (fun a b => dist a b ≤ r) x y := by
      intro x y hxy
      obtain ⟨i, hi⟩ : ∃ i : Fin (Fintype.card X), (componentPart r).label x = i ∧ (componentPart r).label y = i := by
        aesop;
      have h_seq : Relation.ReflTransGen (fun a b => dist a b ≤ r) x (Fintype.equivFin X |>.symm i) ∧ Relation.ReflTransGen (fun a b => dist a b ≤ r) y (Fintype.equivFin X |>.symm i) := by
        exact ⟨ by simpa [ Fin.ext hi.1 ] using Finset.min'_mem ( Finset.filter ( fun i => Relation.ReflTransGen ( fun a b => dist a b ≤ r ) x ( Fintype.equivFin X |>.symm i ) ) Finset.univ ) ⟨ Fintype.equivFin X x, by simp +decide [ Relation.ReflTransGen.refl ] ⟩, by simpa [ Fin.ext hi.2 ] using Finset.min'_mem ( Finset.filter ( fun i => Relation.ReflTransGen ( fun a b => dist a b ≤ r ) y ( Fintype.equivFin X |>.symm i ) ) Finset.univ ) ⟨ Fintype.equivFin X y, by simp +decide [ Relation.ReflTransGen.refl ] ⟩ ⟩;
      have h_symm : ∀ a b : X, Relation.ReflTransGen (fun a b => dist a b ≤ r) a b → Relation.ReflTransGen (fun a b => dist a b ≤ r) b a := by
        intro a b hab; induction hab; aesop;
        rename_i k hk₁ hk₂ hk₃;
        exact hk₃.head ( by simpa [ dist_comm ] using hk₂ );
      exact h_seq.1.trans ( h_symm _ _ h_seq.2 );
    exact fun x y hx hy => reflTransGen_dist_le hr ( h_seq x y ( hx.trans hy.symm ) );
  refine' Metric.ediam_le_of_forall_dist_le _;
  exact fun x hx y hy => le_trans ( h_cluster x y hx hy ) hΔ

/-! ## Bartal's Theorem -/

universe u

/-- Subsingleton spaces admit padded decomposition scheme with β = 0. -/
lemma admitsScheme_subsingleton (X : Type u) [PseudoMetricSpace X] [Subsingleton X]
    (δ : ℝ) : AdmitsPaddedDecompScheme X 0 δ :=
  fun Δ _ => ⟨{
    Ω := ULift.{u} Unit
    msΩ := ⊤
    μ := @Measure.dirac (ULift.{u} Unit) ⊤ ⟨()⟩
    hμ := @Measure.dirac.isProbabilityMeasure (ULift.{u} Unit) ⊤ ⟨()⟩
    partition := fun _ => Partition.trivial
    bounded := fun _ z => by
      simp only [Partition.trivial_cluster]
      calc Metric.ediam (Set.univ : Set X) = 0 := by
            apply le_antisymm _ (zero_le _)
            apply Metric.ediam_le
            intro x _ y _; rw [show x = y from Subsingleton.elim x y, edist_self]
        _ ≤ ENNReal.ofReal Δ := zero_le _
    padding := fun γ _ _ z => by
      simp only [neg_zero, zero_mul, exp_zero, Partition.trivial_cluster]
      simp +decide [Set.subset_univ] }⟩

/-- Helper: Dirac outer measure of the whole space is 1. -/
private lemma dirac_outerMeasure_univ :
    (@Measure.dirac (ULift.{u} Unit) ⊤ ⟨()⟩).toOuterMeasure (Set.univ) = 1 := by
  have : @IsProbabilityMeasure (ULift.{u} Unit) ⊤ (@Measure.dirac (ULift.{u} Unit) ⊤ ⟨()⟩) :=
    @Measure.dirac.isProbabilityMeasure (ULift.{u} Unit) ⊤ ⟨()⟩
  simp [Measure.toOuterMeasure_apply, measure_univ]

/-- **Bartal's Theorem**: Every finite metric space with `n` points admits an
`(O(log n), Ω(1))`-padded decomposition scheme. -/
theorem bartal_padded_decomposition (X : Type u) [MetricSpace X] [Fintype X] :
    ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧
      AdmitsPaddedDecompScheme X (C * Real.log (Fintype.card X)) δ₀ := by
  by_cases hn : Fintype.card X ≤ 1
  · -- For n ≤ 1, X is a subsingleton
    have hsub : Subsingleton X := Fintype.card_le_one_iff_subsingleton.mp hn
    have hlog : Real.log (Fintype.card X : ℝ) = 0 := by
      interval_cases (Fintype.card X) <;> simp [Real.log_zero, Real.log_one]
    refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    rw [hlog, mul_zero]
    exact admitsScheme_subsingleton X 1
  · -- For n ≥ 2
    push_neg at hn
    have hn2 : 2 ≤ Fintype.card X := by omega
    have hn_pos : (0 : ℝ) < (Fintype.card X : ℝ) := by positivity
    refine ⟨1, 1 / (2 * (Fintype.card X : ℝ)), by norm_num, by positivity, ?_⟩
    intro Δ hΔ
    -- Use connected component partition with r = Δ/(2n)
    set n : ℝ := (Fintype.card X : ℝ)
    set r : ℝ := Δ / (2 * n) with hr_def
    have hr_pos : 0 < r := by positivity
    -- Build the padded decomposition
    refine ⟨{
      Ω := ULift.{u} Unit
      msΩ := ⊤
      μ := @Measure.dirac (ULift.{u} Unit) ⊤ ⟨()⟩
      hμ := @Measure.dirac.isProbabilityMeasure (ULift.{u} Unit) ⊤ ⟨()⟩
      partition := fun _ => componentPart (X := X) r
      bounded := fun _ => by
        apply componentPart_isBounded r Δ (le_of_lt hr_pos)
        -- Show (n - 1) * r ≤ Δ
        have h1 : (n - 1) / (2 * n) ≤ 1 := by
          rw [div_le_one (by linarith : (0:ℝ) < 2 * n)]; linarith
        calc (n - 1) * r = (n - 1) * (Δ / (2 * n)) := rfl
          _ = ((n - 1) / (2 * n)) * Δ := by ring
          _ ≤ 1 * Δ := by apply mul_le_mul_of_nonneg_right h1 (le_of_lt hΔ)
          _ = Δ := one_mul Δ
      padding := fun γ hγ0 hγδ z => by
        -- γ * Δ ≤ r, so closedBall z (γ*Δ) ⊆ cluster z
        have hγr : γ * Δ ≤ r := by
          calc γ * Δ ≤ (1 / (2 * n)) * Δ := by
                exact mul_le_mul_of_nonneg_right hγδ (le_of_lt hΔ)
            _ = r := by simp only [hr_def]; ring
        have hsub : Metric.closedBall z (γ * Δ) ⊆ (componentPart (X := X) r).cluster z :=
          fun w hw => componentPart_closedBall_subset r z
            (Metric.closedBall_subset_closedBall hγr hw)
        -- Event = univ, so outer measure = 1 ≥ exp(-β*γ)
        have hset_eq : {ω : ULift.{u} Unit |
            Metric.closedBall z (γ * Δ) ⊆ (componentPart (X := X) r).cluster z} =
            Set.univ :=
          Set.eq_univ_of_forall (fun _ => hsub)
        rw [hset_eq]
        have hn_ge : (1 : ℝ) ≤ n := by
          show (1 : ℝ) ≤ (Fintype.card X : ℝ)
          exact_mod_cast (show 1 ≤ Fintype.card X by omega)
        have hlog_nn : 0 ≤ Real.log n := Real.log_nonneg hn_ge
        calc ENNReal.ofReal (Real.exp (-(1 * Real.log n) * γ))
            ≤ ENNReal.ofReal 1 := by
              apply ENNReal.ofReal_le_ofReal
              exact Real.exp_le_one_iff.mpr (by nlinarith)
          _ = 1 := ENNReal.ofReal_one
          _ = (@Measure.dirac (ULift.{u} Unit) ⊤ ⟨()⟩).toOuterMeasure Set.univ :=
              (dirac_outerMeasure_univ).symm
    }⟩

end

end PaddedDecomposition