import Mathlib
import InducedMinorFreeSeparators.ConcurrentFlowProof.Defs

/-!
# Transitivity of the Induced Minor Relation

We prove that HasInducedMinor is transitive: if G contains K as an induced
minor and K contains H as an induced minor, then G contains H as an
induced minor.
-/

open SimpleGraph

noncomputable section

namespace SimpleGraph

private theorem reachable_within_branch
    {V : Type*} {W : Type*}
    {G : SimpleGraph V} {K : SimpleGraph W}
    (m₁ : InducedMinorModel G K) (S : Set W)
    (w : W) (hw : w ∈ S)
    (v₁ : V) (hv₁ : v₁ ∈ m₁.branch w)
    (v₂ : V) (hv₂ : v₂ ∈ m₁.branch w) :
    (G.induce (⋃ w ∈ S, m₁.branch w)).Reachable
      ⟨v₁, Set.mem_iUnion₂.mpr ⟨w, hw, hv₁⟩⟩
      ⟨v₂, Set.mem_iUnion₂.mpr ⟨w, hw, hv₂⟩⟩ := by
  have h_reachable : (G.induce (m₁.branch w)).Reachable ⟨v₁, hv₁⟩ ⟨v₂, hv₂⟩ :=
    (m₁.branch_connected w) ⟨v₁, hv₁⟩ ⟨v₂, hv₂⟩
  convert h_reachable.map _
  rotate_right
  use fun x => ⟨x.val, Set.mem_iUnion₂.mpr ⟨w, hw, x.property⟩⟩
  all_goals norm_num

private theorem reachable_in_branch_union
    {V : Type*} {W : Type*}
    {G : SimpleGraph V} {K : SimpleGraph W}
    (m₁ : InducedMinorModel G K) (S : Set W)
    (w₁ : W) (hw₁ : w₁ ∈ S) (w₂ : W) (hw₂ : w₂ ∈ S)
    (hrw : (K.induce S).Reachable ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩)
    (v₁ : V) (hv₁ : v₁ ∈ m₁.branch w₁)
    (v₂ : V) (hv₂ : v₂ ∈ m₁.branch w₂) :
    (G.induce (⋃ w ∈ S, m₁.branch w)).Reachable
      ⟨v₁, Set.mem_iUnion₂.mpr ⟨w₁, hw₁, hv₁⟩⟩
      ⟨v₂, Set.mem_iUnion₂.mpr ⟨w₂, hw₂, hv₂⟩⟩ := by
  suffices h_ind : ∀ (u v : ↥S), (K.induce S).Walk u v →
      ∀ (v₁ : V) (hv₁ : v₁ ∈ m₁.branch u.1),
      ∀ (v₂ : V) (hv₂ : v₂ ∈ m₁.branch v.1),
      (G.induce (⋃ w ∈ S, m₁.branch w)).Reachable
        ⟨v₁, Set.mem_iUnion₂.mpr ⟨u.1, u.2, hv₁⟩⟩
        ⟨v₂, Set.mem_iUnion₂.mpr ⟨v.1, v.2, hv₂⟩⟩ by
    exact h_ind ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ hrw.some v₁ hv₁ v₂ hv₂
  intro u v a
  induction a with
  | nil => intro v₁ hv₁ v₂ hv₂; exact reachable_within_branch m₁ S _ (Subtype.mem _) v₁ hv₁ v₂ hv₂
  | @cons x y z hadj _ ih =>
    intro v₁ hv₁ v₂ hv₂
    obtain ⟨x₁, hx₁, x₂, hx₂, h_adj⟩ := m₁.adj_preserved _ _ hadj
    have hr1 := reachable_within_branch m₁ S x x.2 v₁ hv₁ x₁ hx₁
    have hr2 : (G.induce (⋃ w ∈ S, m₁.branch w)).Reachable
        ⟨x₁, Set.mem_iUnion₂.mpr ⟨x.1, x.2, hx₁⟩⟩
        ⟨x₂, Set.mem_iUnion₂.mpr ⟨y.1, y.2, hx₂⟩⟩ :=
      SimpleGraph.Adj.reachable (by aesop)
    have hr3 := ih x₂ hx₂ v₂ hv₂
    exact hr1.trans (hr2.trans hr3)

theorem HasInducedMinor.trans {V : Type*} {W : Type*} {U : Type*}
    {G : SimpleGraph V} {K : SimpleGraph W} {H : SimpleGraph U}
    (hGK : HasInducedMinor G K) (hKH : HasInducedMinor K H) :
    HasInducedMinor G H := by
  obtain ⟨m₁⟩ := hGK
  obtain ⟨m₂⟩ := hKH
  refine ⟨⟨fun u => ⋃ w ∈ m₂.branch u, m₁.branch w, ?_, ?_, ?_, ?_⟩⟩
  · -- Connected
    intro u
    simp [SimpleGraph.connected_iff_exists_forall_reachable]
    obtain ⟨w₀, hw₀⟩ := (m₂.branch_connected u).nonempty
    obtain ⟨v₀, hv₀⟩ := (m₁.branch_connected w₀).nonempty
    refine ⟨v₀, ⟨w₀, hw₀, hv₀⟩, fun v₁ w₁ hw₁ hv₁ => ?_⟩
    exact reachable_in_branch_union m₁ (m₂.branch u) w₀ hw₀ w₁ hw₁
      ((m₂.branch_connected u) ⟨w₀, hw₀⟩ ⟨w₁, hw₁⟩) v₀ hv₀ v₁ hv₁
  · -- Disjoint
    intro u₁ u₂ hne
    simp +decide [Set.disjoint_left]
    intro v w₁ hw₁ hv₁ w₂ hw₂ hv₂
    exact Set.disjoint_left.mp
      (m₁.branch_disjoint w₁ w₂ (by
        rintro rfl
        exact hne (by
          have := Set.disjoint_left.mp (m₂.branch_disjoint _ _ hne) hw₁ hw₂
          contradiction)))
      hv₁ hv₂
  · -- Adjacency preserved
    intro u₁ u₂ hadj
    obtain ⟨w₁, hw₁, w₂, hw₂, hwe⟩ := m₂.adj_preserved u₁ u₂ hadj
    obtain ⟨v₁, hv₁, v₂, hv₂, hv⟩ := m₁.adj_preserved w₁ w₂ hwe
    exact ⟨v₁, Set.mem_iUnion₂.mpr ⟨w₁, hw₁, hv₁⟩,
           v₂, Set.mem_iUnion₂.mpr ⟨w₂, hw₂, hv₂⟩, hv⟩
  · -- Non-adjacency preserved
    intro u₁ u₂ hne hnadj v₁ hv₁ v₂ hv₂
    obtain ⟨w₁, hw₁, hw₁'⟩ := Set.mem_iUnion₂.mp hv₁
    obtain ⟨w₂, hw₂, hw₂'⟩ := Set.mem_iUnion₂.mp hv₂
    have hw : w₁ ≠ w₂ := by
      intro h; subst h
      exact hne (by
        have := Set.disjoint_left.mp (m₂.branch_disjoint u₁ u₂ hne) hw₁ hw₂
        contradiction)
    exact m₁.nonadj_preserved w₁ w₂ hw
      (m₂.nonadj_preserved u₁ u₂ hne hnadj w₁ hw₁ w₂ hw₂) v₁ hw₁' v₂ hw₂'

end SimpleGraph
end
