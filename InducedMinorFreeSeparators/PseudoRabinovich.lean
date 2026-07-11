/-
# Rabinovich's Average-Distortion Embedding for Pseudometric Spaces

The padded-decomposition development (`Padding/`) proves Rabinovich's
average-distortion embedding theorem for finite metric spaces
(`MainResults.rabinovich_embedding`). For the separator application we need the
same statement for a finite pseudometric space, since the vertex-weighted
shortest-path pseudometric can assign distance `0` to distinct vertices.

The proof perturbs the pseudometric to a genuine metric `d + ε·[x ≠ y]`, applies
the metric version, and takes the limit `ε → 0` via a compactness argument.
-/
import Mathlib
import Padding.MainRabinovich

open Finset BigOperators
open scoped Classical

namespace PseudoRabinovich

noncomputable section

variable {X : Type*}

/-! ## A metric space from a distance function -/

/-- Build a `MetricSpace` from a distance function on a finite type satisfying the
metric axioms, including `eq_of_dist_eq_zero`. -/
def mkMS [Fintype X] (d : X → X → ℝ)
    (h1 : ∀ x, d x x = 0) (h2 : ∀ x y, d x y = d y x)
    (h3 : ∀ x y z, d x z ≤ d x y + d y z)
    (h4 : ∀ x y, d x y = 0 → x = y) : MetricSpace X where
  dist := d
  dist_self := h1
  dist_comm := h2
  dist_triangle := h3
  eq_of_dist_eq_zero := fun {x y} h => h4 x y h
  edist := fun x y => ENNReal.ofReal (d x y)
  edist_dist := fun _ _ => rfl
  toUniformSpace := UniformSpace.ofDist d h1 h2 h3
  uniformity_dist := rfl
  toBornology := @Bornology.mk X (Filter.cofinite) (le_refl _)
  cobounded_sets := by
    simp +decide [Bornology.cobounded]
    ext s
    constructor
    · intro _
      use sSup (Set.range (fun p : X × X => d p.1 p.2))
      exact fun x _ y _ =>
        le_csSup (Set.finite_range _ |> Set.Finite.bddAbove) (Set.mem_range_self (x, y))
    · aesop

/-! ## The epsilon-perturbed metric -/

variable [PseudoMetricSpace X]

/-- The perturbed distance `d(x,y) + ε·[x ≠ y]`. -/
def pertDist (ε : ℝ) (x y : X) : ℝ := dist x y + (if x = y then 0 else ε)

lemma pertDist_self (ε : ℝ) (x : X) : pertDist ε x x = 0 := by
  simp [pertDist]

lemma pertDist_comm (ε : ℝ) (x y : X) : pertDist ε x y = pertDist ε y x := by
  unfold pertDist
  rw [dist_comm]
  by_cases h : x = y <;> simp [h, eq_comm]

lemma pertDist_triangle (ε : ℝ) (hε : 0 ≤ ε) (x y z : X) :
    pertDist ε x z ≤ pertDist ε x y + pertDist ε y z := by
  unfold pertDist
  rcases eq_or_ne x z with hxz | hxz <;>
    rcases eq_or_ne x y with hxy | hxy <;>
    rcases eq_or_ne y z with hyz | hyz <;>
    simp_all [dist_comm] <;>
    nlinarith [dist_nonneg (x := x) (y := y), dist_nonneg (x := y) (y := z),
      dist_nonneg (x := x) (y := z), dist_triangle x y z]

lemma pertDist_eq_zero (ε : ℝ) (hε : 0 < ε) (x y : X) (h : pertDist ε x y = 0) :
    x = y := by
  by_contra hne
  simp only [pertDist, if_neg hne] at h
  nlinarith [dist_nonneg (x := x) (y := y)]

lemma pertDist_ge_dist (ε : ℝ) (hε : 0 ≤ ε) (x y : X) : dist x y ≤ pertDist ε x y := by
  unfold pertDist
  by_cases h : x = y <;> simp [h, hε]

lemma pertDist_le_dist_add (ε : ℝ) (hε : 0 ≤ ε) (x y : X) :
    pertDist ε x y ≤ dist x y + ε := by
  unfold pertDist
  by_cases h : x = y <;> simp [h, hε]

variable [Fintype X]

/-- The `MetricSpace` structure given by the epsilon-perturbed distance, for `ε > 0`. -/
def pertMetricSpace (ε : ℝ) (hε : 0 < ε) : MetricSpace X :=
  mkMS (pertDist ε) (pertDist_self ε) (pertDist_comm ε)
    (pertDist_triangle ε hε.le) (pertDist_eq_zero ε hε)

/-! ## Per-epsilon embedding from the metric version -/

/-- The metric version of Rabinovich's theorem, applied to the epsilon-perturbed
metric and re-expressed using the raw `pertDist` double sums. -/
lemma rabinovich_pert (ε : ℝ) (hε : 0 < ε) :
    ∃ g : X → ℝ, (∀ x y, |g x - g y| ≤ pertDist ε x y) ∧
      (∑ x : X, ∑ y : X, pertDist ε x y) ≤
        1280 * Real.log (Fintype.card X) * (∑ x : X, ∑ y : X, |g x - g y|) := by
  obtain ⟨g, hne, hbd⟩ := @MainResults.rabinovich_embedding X (pertMetricSpace ε hε) _
  exact ⟨g, fun x y => hne x y, hbd⟩

/-- Applying Rabinovich's theorem to the epsilon-perturbed metric and translating
so the base point maps to `0`. -/
lemma perturbed_embedding (ε : ℝ) (hε : 0 < ε) (x₀ : X) :
    ∃ f : X → ℝ,
      (∀ x y, |f x - f y| ≤ dist x y + ε) ∧
      (∑ x : X, ∑ y : X, dist x y) ≤
        1280 * Real.log (Fintype.card X) * (∑ x : X, ∑ y : X, |f x - f y|) ∧
      (∀ x, |f x| ≤ dist x x₀ + ε) ∧
      f x₀ = 0 := by
  obtain ⟨g, hne, hbd⟩ := rabinovich_pert (X := X) ε hε
  refine ⟨fun x => g x - g x₀, ?_, ?_, ?_, ?_⟩
  · intro x y
    have h : g x - g x₀ - (g y - g x₀) = g x - g y := by ring
    rw [h]
    exact (hne x y).trans (pertDist_le_dist_add ε hε.le x y)
  · have heq : ∀ x y : X, |g x - g x₀ - (g y - g x₀)| = |g x - g y| := by
      intro x y
      congr 1
      ring
    calc (∑ x : X, ∑ y : X, dist x y)
        ≤ ∑ x : X, ∑ y : X, pertDist ε x y :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
            pertDist_ge_dist ε hε.le x y
      _ ≤ 1280 * Real.log (Fintype.card X) * (∑ x : X, ∑ y : X, |g x - g y|) := hbd
      _ = 1280 * Real.log (Fintype.card X) *
            (∑ x : X, ∑ y : X, |g x - g x₀ - (g y - g x₀)|) := by simp_rw [heq]
  · intro x
    exact (hne x x₀).trans (pertDist_le_dist_add ε hε.le x x₀)
  · ring

/-! ## The compactness limit -/

/-- The compactness/limit core of `pseudometric_rabinovich`, assuming `X` is
nonempty so that a base point is available for the normalization. -/
lemma pseudometric_rabinovich_nonempty [Nonempty X] :
    ∃ f : X → ℝ,
      (∀ x y, |f x - f y| ≤ dist x y) ∧
      (∑ x : X, ∑ y : X, dist x y) ≤
        1280 * Real.log (Fintype.card X) * (∑ x : X, ∑ y : X, |f x - f y|) := by
  have h_seq_compact :
      IsCompact (Set.pi Set.univ
        (fun x : X => Set.Icc (-(dist x (Classical.arbitrary X) + 1))
          (dist x (Classical.arbitrary X) + 1))) := by
    exact isCompact_univ_pi fun x => CompactIccSpace.isCompact_Icc
  obtain ⟨f, hf⟩ : ∃ f ∈ Set.pi Set.univ
      (fun x : X => Set.Icc (-(dist x (Classical.arbitrary X) + 1))
        (dist x (Classical.arbitrary X) + 1)),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Filter.Tendsto
          (fun j => (fun x =>
            (Classical.choose
              (perturbed_embedding (1 / (φ j + 1)) (by positivity)
                (Classical.arbitrary X))) x) : ℕ → X → ℝ)
          Filter.atTop (nhds f) := by
    have := h_seq_compact.isSeqCompact fun n =>
      show (fun x =>
          Classical.choose
            (perturbed_embedding (1 / (n + 1)) (by positivity) (Classical.arbitrary X)) x)
        ∈ Set.pi Set.univ
            (fun x => Set.Icc (-(dist x (Classical.arbitrary X) + 1))
              (dist x (Classical.arbitrary X) + 1)) from ?_
    · tauto
    · intro x _
      have := Classical.choose_spec
        (perturbed_embedding (1 / (n + 1)) (by positivity) (Classical.arbitrary X))
      simp_all +decide [abs_le]
      constructor <;>
        nlinarith [this.2.2.1 x, inv_mul_cancel₀ (by linarith : (n : ℝ) + 1 ≠ 0)]
  have h_nonexpansive : ∀ x y : X, |f x - f y| ≤ dist x y := by
    intro x y
    have h_lim :
        Filter.Tendsto
          (fun j => |(Classical.choose
              (perturbed_embedding (1 / (hf.right.choose j + 1)) (by positivity)
                (Classical.arbitrary X))) x -
            (Classical.choose
              (perturbed_embedding (1 / (hf.right.choose j + 1)) (by positivity)
                (Classical.arbitrary X))) y|)
          Filter.atTop (nhds (|f x - f y|)) := by
      exact Filter.Tendsto.abs
        (Filter.Tendsto.sub (tendsto_pi_nhds.mp hf.2.choose_spec.2 x)
          (tendsto_pi_nhds.mp hf.2.choose_spec.2 y))
    have h_lim_le : ∀ j,
        |(Classical.choose
            (perturbed_embedding (1 / (hf.right.choose j + 1)) (by positivity)
              (Classical.arbitrary X))) x -
          (Classical.choose
            (perturbed_embedding (1 / (hf.right.choose j + 1)) (by positivity)
              (Classical.arbitrary X))) y| ≤
          dist x y + 1 / (hf.right.choose j + 1) := by
      intro j
      have := Classical.choose_spec
        (perturbed_embedding (1 / (hf.right.choose j + 1)) (by positivity)
          (Classical.arbitrary X))
      aesop
    exact le_of_tendsto_of_tendsto' h_lim
      (tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hf.2.choose_spec.1.tendsto_atTop))
      h_lim_le |> le_trans <| by simp +decide
  refine' ⟨f, h_nonexpansive, _⟩
  obtain ⟨φ, hφ₁, hφ₂⟩ := hf.2
  have h_sum_bound : ∀ j,
      (∑ x : X, ∑ y : X, dist x y) ≤
        1280 * Real.log (Fintype.card X) *
          (∑ x : X, ∑ y : X,
            |(Classical.choose
              (perturbed_embedding (1 / (φ j + 1)) (by positivity)
                (Classical.arbitrary X))) x -
              (Classical.choose
                (perturbed_embedding (1 / (φ j + 1)) (by positivity)
                  (Classical.arbitrary X))) y|) := by
    exact fun j => Classical.choose_spec
      (perturbed_embedding (1 / (φ j + 1)) (by positivity) (Classical.arbitrary X)) |>.2.1
  have h_sum_tendsto :
      Filter.Tendsto
        (fun j => ∑ x : X, ∑ y : X,
          |(Classical.choose
            (perturbed_embedding (1 / (φ j + 1)) (by positivity)
              (Classical.arbitrary X))) x -
            (Classical.choose
              (perturbed_embedding (1 / (φ j + 1)) (by positivity)
                (Classical.arbitrary X))) y|)
        Filter.atTop (nhds (∑ x : X, ∑ y : X, |f x - f y|)) := by
    exact tendsto_finset_sum _ fun x _ => tendsto_finset_sum _ fun y _ =>
      Filter.Tendsto.abs
        (Filter.Tendsto.sub (tendsto_pi_nhds.mp hφ₂ x) (tendsto_pi_nhds.mp hφ₂ y))
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds (h_sum_tendsto.const_mul _) h_sum_bound

/-- **Rabinovich's average-distortion embedding for pseudometric spaces.**
Every finite pseudometric space admits a non-expansive embedding
`f : X → ℝ` with `∑∑ d(x,y) ≤ 1280 · log n · ∑∑ |f x - f y|`. -/
theorem pseudometric_rabinovich :
    ∃ f : X → ℝ,
      (∀ x y, |f x - f y| ≤ dist x y) ∧
      (∑ x : X, ∑ y : X, dist x y) ≤
        1280 * Real.log (Fintype.card X) * (∑ x : X, ∑ y : X, |f x - f y|) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨fun _ => 0, fun x y => hX.elim x, by simp⟩
  · exact pseudometric_rabinovich_nonempty

end

end PseudoRabinovich
