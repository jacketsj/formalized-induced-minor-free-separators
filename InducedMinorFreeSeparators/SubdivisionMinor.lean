/- # A graph is an induced minor of its one-subdivision -/
import InducedMinorFreeSeparators.ResidualStructural

open Set Function SimpleGraph
open scoped Classical

noncomputable section

variable {h : ℕ} (H : SimpleGraph (Fin h))

/-- Choose one endpoint to own each subdivision vertex. -/
private def subdivisionOwner (e : H.edgeSet) : Fin h :=
  e.1.toFinset.min' (e.1.inductionOn fun u v => by simp [Sym2.toFinset_mk_eq])

private lemma subdivisionOwner_mem (e : H.edgeSet) : subdivisionOwner H e ∈ e.1 := by
  rw [← Sym2.mem_toFinset]
  exact Finset.min'_mem _ _

/-- Branch set obtained by assigning each subdivision vertex to one of its
endpoints. -/
private def subdivisionBranch (v : Fin h) : Set ((Fin h) ⊕ H.edgeSet) :=
  {Sum.inl v} ∪ {x | ∃ e : H.edgeSet, x = Sum.inr e ∧ subdivisionOwner H e = v}

/-- Contracting every subdivision vertex toward its chosen owner recovers the
original graph as an induced minor. -/
theorem graphOneSubdiv_has_original_induced_minor :
    HasInducedMinor_internal (graphOneSubdiv H) H := by
  refine ⟨⟨subdivisionBranch H, ?_, ?_, ?_, ?_⟩⟩
  · intro v
    refine SimpleGraph.connected_iff_exists_forall_reachable _ |>.2
      ⟨⟨Sum.inl v, by simp [subdivisionBranch]⟩, ?_⟩
    rintro ⟨x, hx⟩
    rcases hx with hx | hx
    · subst x
      exact ⟨SimpleGraph.Walk.nil⟩
    · obtain ⟨e, rfl, he⟩ := hx
      refine ⟨SimpleGraph.Walk.cons ?_ SimpleGraph.Walk.nil⟩
      simp only [SimpleGraph.induce_adj, graphOneSubdiv]
      exact he ▸ subdivisionOwner_mem H e
  · intro u v huv
    rw [Set.disjoint_left]
    intro x hxu hxv
    rcases hxu with hxu | hxu <;> rcases hxv with hxv | hxv
    · simp_all [subdivisionBranch]
    · obtain ⟨e, heq, _⟩ := hxv
      simp_all
    · obtain ⟨e, heq, _⟩ := hxu
      simp_all
    · obtain ⟨e, rfl, heu⟩ := hxu
      obtain ⟨f, hef, hev⟩ := hxv
      simp only [Sum.inr.injEq] at hef
      subst f
      exact huv (heu.symm.trans hev)
  · intro u v huv
    let e : H.edgeSet := ⟨s(u, v), by simpa [SimpleGraph.mem_edgeSet] using huv⟩
    have hou : subdivisionOwner H e = u ∨ subdivisionOwner H e = v := by
      have := subdivisionOwner_mem H e
      simpa [e, Sym2.mem_iff] using this
    rcases hou with hou | hov
    · refine ⟨Sum.inr e, ?_, Sum.inl v, ?_, ?_⟩
      · exact Or.inr ⟨e, rfl, hou⟩
      · exact Or.inl rfl
      · simp [graphOneSubdiv, e]
    · refine ⟨Sum.inl u, ?_, Sum.inr e, ?_, ?_⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨e, rfl, hov⟩
      · simp [graphOneSubdiv, e]
  · intro u v huv hnuv x hxu y hyv
    rcases hxu with hxu | hxu <;> rcases hyv with hyv | hyv
    · subst x
      subst y
      simp [graphOneSubdiv]
    · subst x
      obtain ⟨e, rfl, hev⟩ := hyv
      simp only [graphOneSubdiv]
      intro hue
      have hvE : v ∈ e.1 := hev ▸ subdivisionOwner_mem H e
      have heq : e.1 = s(u, v) := (Sym2.mem_and_mem_iff huv).mp ⟨hue, hvE⟩
      exact hnuv (by
        have : s(u, v) ∈ H.edgeSet := heq ▸ e.2
        simpa [SimpleGraph.mem_edgeSet] using this)
    · obtain ⟨e, rfl, heu⟩ := hxu
      subst y
      simp only [graphOneSubdiv]
      intro hve
      have huE : u ∈ e.1 := heu ▸ subdivisionOwner_mem H e
      have heq : e.1 = s(u, v) := (Sym2.mem_and_mem_iff huv).mp ⟨huE, hve⟩
      exact hnuv (by
        have : s(u, v) ∈ H.edgeSet := heq ▸ e.2
        simpa [SimpleGraph.mem_edgeSet] using this)
    · obtain ⟨e, rfl, _⟩ := hxu
      obtain ⟨f, rfl, _⟩ := hyv
      simp [graphOneSubdiv]

/-- An edgeless graph on the original vertices is an induced minor of the
one-subdivision of any graph on those vertices: keep only the original
vertices as singleton branch sets. -/
theorem graphOneSubdiv_has_edgeless_induced_minor
    (F : SimpleGraph (Fin h)) (hH : H = ⊥) :
    HasInducedMinor_internal (graphOneSubdiv F) H := by
  subst H
  refine ⟨⟨fun v => {Sum.inl v}, ?_, ?_, ?_, ?_⟩⟩
  · intro v
    simp
  · intro u v huv
    simp only [Set.disjoint_singleton]
    exact fun heq => huv (Sum.inl.inj heq)
  · simp
  · intro u v _ _ x hx y hy
    subst x
    subst y
    simp [graphOneSubdiv]

end
