/-
# Vertex-Weighted Shortest Path (VWSP) Metric

Additional definitions and lemmas for the VWSP pseudometric on a connected graph
with nonneg vertex weights. Both endpoint-heavy (each edge contributes w(u) + w(v))
and endpoint-light (each edge contributes (w(u) + w(v))/2) variants are provided.

The core definitions (`SimpleGraph.Walk.edgeWeightSum`, `SimpleGraph.weightedDist`,
`pairDistSum`) live in `Defs.lean`; this file provides `mkPMS`, `vwspPMS`, and the
endpoint-light variant.
-/
import InducedMinorFreeSeparators.ProofDefs

open Set Function
open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V]

/-! ## PseudoMetricSpace construction -/

omit [Fintype V] in
/-- Construct a PseudoMetricSpace from a distance function on a finite type. -/
noncomputable def mkPMS (d : V → V → ℝ)
    (h1 : ∀ x, d x x = 0) (h2 : ∀ x y, d x y = d y x)
    (h3 : ∀ x y z, d x z ≤ d x y + d y z) : PseudoMetricSpace V where
  dist := d
  dist_self := h1
  dist_comm := h2
  dist_triangle := h3
  edist := fun x y => ENNReal.ofReal (d x y)
  edist_dist := fun _ _ => rfl
  toUniformSpace := UniformSpace.ofDist d h1 h2 h3
  uniformity_dist := rfl
  toBornology := @Bornology.mk V (Filter.cofinite) (le_refl _)
  cobounded_sets := by
    simp +decide [Bornology.cobounded]
    ext s
    constructor
    · intro _
      use sSup (Set.range (fun p : V × V => d p.1 p.2))
      exact fun x _ y _ =>
        le_csSup (Set.finite_range _ |> Set.Finite.bddAbove) (Set.mem_range_self (x, y))
    · aesop

/-! ## Helper: edge weight sum nonnegativity -/

omit [Fintype V] in
/-- Edge weight sum is nonneg when weights are nonneg. -/
lemma edgeWeightSum_nonneg {G : SimpleGraph V} {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) {u v : V} (p : G.Walk u v) :
    0 ≤ p.edgeWeightSum w := by
  induction p with
  | nil => simp [SimpleGraph.Walk.edgeWeightSum]
  | @cons u' v' w' _ _ ih =>
    simp only [SimpleGraph.Walk.edgeWeightSum]
    linarith [hw u', hw v']

/-! ## VWSP metric axioms (endpoint-heavy) -/

omit [Fintype V] in
/-- The VWSP distance is self-zero. -/

lemma weightedDist_self' {G : SimpleGraph V} {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) (v : V) :
    G.weightedDist w v v = 0 := by
  apply le_antisymm
  · exact ciInf_le ⟨0, Set.forall_mem_range.mpr (fun p => edgeWeightSum_nonneg hw p)⟩
      (SimpleGraph.Walk.nil (u := v))
  · exact le_ciInf fun p => edgeWeightSum_nonneg hw p

omit [Fintype V] in
/-- Edge weight sum is additive over walk append. -/
lemma edgeWeightSum_append' {G : SimpleGraph V} (w : V → ℝ)
    {u v z : V} (p : G.Walk u v) (q : G.Walk v z) :
    (p.append q).edgeWeightSum w = p.edgeWeightSum w + q.edgeWeightSum w := by
  induction p with
  | nil => simp [SimpleGraph.Walk.edgeWeightSum]
  | cons _ _ ih => simp [SimpleGraph.Walk.edgeWeightSum, ih]; ring

omit [Fintype V] in
/-- Edge weight sum is preserved under walk reversal. -/

lemma edgeWeightSum_reverse' {G : SimpleGraph V} (w : V → ℝ)
    {u v : V} (p : G.Walk u v) :
    p.reverse.edgeWeightSum w = p.edgeWeightSum w := by
  induction p with
  | nil => simp [SimpleGraph.Walk.edgeWeightSum]
  | @cons u' v' w' _ _ ih =>
    rw [SimpleGraph.Walk.reverse_cons, edgeWeightSum_append']
    simp only [SimpleGraph.Walk.edgeWeightSum]
    linarith

omit [Fintype V] in
/-- The VWSP distance is symmetric (by walk reversal). -/

lemma weightedDist_symm {G : SimpleGraph V} (w : V → ℝ)
    (u v : V) :
    G.weightedDist w u v = G.weightedDist w v u := by
  unfold SimpleGraph.weightedDist
  apply Equiv.iInf_congr
    ⟨fun p => p.reverse, fun p => p.reverse,
      fun p => by simp, fun p => by simp⟩
  intro p
  simp only [Equiv.coe_fn_mk]
  exact edgeWeightSum_reverse' w p

omit [Fintype V] in
/-- The VWSP distance satisfies the triangle inequality. -/

lemma weightedDist_triangle' {G : SimpleGraph V} {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) (hconn : G.Connected) (u v z : V) :
    G.weightedDist w u z ≤ G.weightedDist w u v + G.weightedDist w v z := by
  have h1 : ∀ p : G.Walk u v,
      G.weightedDist w u z ≤ p.edgeWeightSum w + G.weightedDist w v z := by
    intro p
    rw [forall_gt_imp_ge_iff_le_of_dense.symm]
    intro x hx
    have hne : Nonempty (G.Walk v z) := ⟨(hconn v z).some⟩
    obtain ⟨q, hq⟩ := exists_lt_of_ciInf_lt
      (show G.weightedDist w v z < x - p.edgeWeightSum w by linarith)
    have : G.weightedDist w u z ≤ p.edgeWeightSum w + q.edgeWeightSum w := by
      calc G.weightedDist w u z
          ≤ (p.append q).edgeWeightSum w :=
            ciInf_le ⟨0, Set.forall_mem_range.2 (edgeWeightSum_nonneg hw)⟩ (p.append q)
        _ = _ := edgeWeightSum_append' w p q
    linarith
  rw [forall_gt_imp_ge_iff_le_of_dense.symm]
  intro x hx
  have hne : Nonempty (G.Walk u v) := ⟨(hconn u v).some⟩
  obtain ⟨p, hp⟩ := exists_lt_of_ciInf_lt
    (show G.weightedDist w u v < x - G.weightedDist w v z by linarith)
  linarith [h1 p]

omit [Fintype V] in
/-- For an edge uv, the VWSP distance is at most w(u) + w(v). -/

lemma weightedDist_le_edge {G : SimpleGraph V} {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) {u v : V} (hadj : G.Adj u v) :
    G.weightedDist w u v ≤ w u + w v := by
  apply csInf_le
  · exact ⟨0, Set.forall_mem_range.2 (edgeWeightSum_nonneg hw)⟩
  · exact ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil,
      by simp [SimpleGraph.Walk.edgeWeightSum]⟩

/-- The VWSP PseudoMetricSpace on V for connected G with nonneg weights. -/
noncomputable def vwspPMS (G : SimpleGraph V) (w : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hconn : G.Connected) : PseudoMetricSpace V :=
  mkPMS (G.weightedDist w) (weightedDist_self' hw) (weightedDist_symm w)
    (weightedDist_triangle' hw hconn)

/-! ## Endpoint-light (half-weight) variant -/

/-- Endpoint-light edge weight sum: each edge contributes (w(u) + w(v)) / 2. -/
def SimpleGraph.Walk.edgeWeightSumLight {G : SimpleGraph V} (w : V → ℝ) :
    {u v : V} → G.Walk u v → ℝ
  | _, _, .nil => 0
  | u, _, .cons (v := v) _ p => (w u + w v) / 2 + p.edgeWeightSumLight w

/-- Endpoint-light VWSP distance. -/
noncomputable def SimpleGraph.weightedDistLight (G : SimpleGraph V) (w : V → ℝ) (u v : V) : ℝ :=
  ⨅ (p : G.Walk u v), p.edgeWeightSumLight w

omit [Fintype V] in
/-- The light edge weight sum is exactly half the heavy one. -/
lemma edgeWeightSumLight_eq_half {G : SimpleGraph V} (w : V → ℝ)
    {u v : V} (p : G.Walk u v) :
    p.edgeWeightSumLight w = p.edgeWeightSum w / 2 := by
  induction p with
  | nil => simp [SimpleGraph.Walk.edgeWeightSumLight, SimpleGraph.Walk.edgeWeightSum]
  | cons _ _ ih =>
    simp only [SimpleGraph.Walk.edgeWeightSumLight, SimpleGraph.Walk.edgeWeightSum, ih]
    ring

omit [Fintype V] in
/-- The light weighted distance is exactly half the heavy one. -/
lemma weightedDistLight_eq_half {G : SimpleGraph V} (w : V → ℝ) (u v : V) :
    G.weightedDistLight w u v = G.weightedDist w u v / 2 := by
  simp only [SimpleGraph.weightedDistLight, SimpleGraph.weightedDist]
  rw [show (fun p : G.Walk u v => p.edgeWeightSumLight w) =
    (fun p => p.edgeWeightSum w / 2) from funext (edgeWeightSumLight_eq_half w)]
  rw [show (fun p : G.Walk u v => p.edgeWeightSum w / 2) =
    (fun p => p.edgeWeightSum w * 2⁻¹) from funext (fun p => by ring)]
  rw [← Real.iInf_mul_of_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  ring

omit [Fintype V] in
/-- Light edge weight sum nonneg. -/

lemma edgeWeightSumLight_nonneg {G : SimpleGraph V} {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) {u v : V} (p : G.Walk u v) :
    0 ≤ p.edgeWeightSumLight w := by
  rw [edgeWeightSumLight_eq_half]
  exact div_nonneg (edgeWeightSum_nonneg hw p) (by norm_num)

omit [Fintype V] in
/-- For an edge uv, the light VWSP distance is at most (w u + w v) / 2. -/
lemma weightedDistLight_le_edge {G : SimpleGraph V} {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) {u v : V} (hadj : G.Adj u v) :
    G.weightedDistLight w u v ≤ (w u + w v) / 2 := by
  rw [weightedDistLight_eq_half]
  exact div_le_div_of_nonneg_right (weightedDist_le_edge hw hadj) (by norm_num : (0 : ℝ) ≤ 2)

/-- The light VWSP PseudoMetricSpace. -/
noncomputable def vwspPMSLight (G : SimpleGraph V) (w : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hconn : G.Connected) : PseudoMetricSpace V :=
  mkPMS (G.weightedDistLight w)
    (fun v => by rw [weightedDistLight_eq_half]; simp [weightedDist_self' hw])
    (fun u v => by simp [weightedDistLight_eq_half, weightedDist_symm])
    (fun u v z => by
      simp only [weightedDistLight_eq_half]
      have := weightedDist_triangle' hw hconn u v z
      linarith)

end
