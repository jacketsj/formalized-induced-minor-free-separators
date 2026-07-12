/- # Improved separator theorem for an arbitrary forbidden graph -/
import InducedMinorFreeSeparators.ImprovedEmbedding
import InducedMinorFreeSeparators.ImprovedSeparatorTransfer
import InducedMinorFreeSeparators.SubdivisionMinor
import InducedMinorFreeSeparators.ConcurrentFlowProof.InducedMinorTrans

open Finset BigOperators
open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem internal_to_public_hasInducedMinor
    {A B : Type*} {G : SimpleGraph A} {H : SimpleGraph B}
    (hm : HasInducedMinor_internal G H) : HasInducedMinor G H := by
  obtain ⟨m⟩ := hm
  exact ⟨⟨m.branch, m.branch_connected, m.branch_disjoint,
    m.adj_preserved, m.nonadj_preserved⟩⟩

private lemma edgeSet_ncard_eq_edgeFinset_card
    {h : ℕ} (H : SimpleGraph (Fin h)) [DecidableRel H.Adj] :
    H.edgeSet.ncard = H.edgeFinset.card := by
  rw [Set.ncard_eq_toFinset_card']
  rfl

private theorem embedding_from_auxiliary
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hconn : G.Connected)
    (h : ℕ) (hh : 2 ≤ h)
    (H : SimpleGraph (Fin h))
    (F : SimpleGraph (Fin h)) (qF : ℕ)
    (hmF : F.edgeSet.ncard = qF) (hqF : 1 ≤ qF)
    (hFH : HasInducedMinor_internal (graphOneSubdiv F) H)
    (hfree : ¬G.ContainsInducedMinor H)
    (hn : 2 ≤ Fintype.card V) :
    ∃ f : V → ℝ,
      (∀ u v, |f u - f v| ≤ G.weightedDist w u v) ∧
      (∑ u : V, ∑ v : V, G.weightedDist w u v ≤
        65536 * Real.log (8 * ((3 * h + qF + 7 : ℕ) : ℝ)) *
          ∑ u : V, ∑ v : V, |f u - f v|) := by
  have hinternal : ¬HasInducedMinor_internal G (graphOneSubdiv F) := by
    intro hsubdiv
    apply hfree
    have h₁ : HasInducedMinor G (graphOneSubdiv F) :=
      internal_to_public_hasInducedMinor hsubdiv
    have h₂ : HasInducedMinor (graphOneSubdiv F) H :=
      internal_to_public_hasInducedMinor hFH
    exact hasInducedMinor_imp_containsInducedMinor
      (SimpleGraph.HasInducedMinor.trans h₁ h₂)
  exact logarithmic_vwsp_embedding_internal G w hw hconn h qF hh hqF F hmF
    hinternal hn

/-- **Improved logarithmic embedding theorem.** For every arbitrary
`h`-vertex forbidden induced minor `H`, the endpoint-heavy vertex-weighted
shortest-path metric admits a line embedding whose distortion depends only
logarithmically on `h + |E(H)|`. -/
theorem improved_embedding_theorem_arbitrary
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hconn : G.Connected)
    (h : ℕ) (hh : 2 ≤ h)
    (H : SimpleGraph (Fin h)) [DecidableRel H.Adj]
    (hfree : ¬G.ContainsInducedMinor H) :
    ∃ f : V → ℝ,
      (∀ u v, |f u - f v| ≤ G.weightedDist w u v) ∧
      (∑ u : V, ∑ v : V, G.weightedDist w u v ≤
        65536 * Real.log
          (8 * ((3 * h + max 1 H.edgeFinset.card + 7 : ℕ) : ℝ)) *
            ∑ u : V, ∑ v : V, |f u - f v|) := by
  by_cases hn : 2 ≤ Fintype.card V
  · by_cases hq : 1 ≤ H.edgeFinset.card
    · simpa [max_eq_right hq] using embedding_from_auxiliary G w hw hconn h hh H H
        H.edgeFinset.card (edgeSet_ncard_eq_edgeFinset_card H) hq
        (graphOneSubdiv_has_original_induced_minor H) hfree hn
    · have hq0 : H.edgeFinset.card = 0 := by omega
      have hHbot : H = ⊥ := by
        apply SimpleGraph.ext
        funext u v
        apply propext
        constructor
        · intro huv
          have he : s(u, v) ∈ H.edgeFinset := by simpa using huv
          rw [Finset.card_eq_zero.mp hq0] at he
          simp at he
        · simp
      let u : Fin h := ⟨0, by omega⟩
      let v : Fin h := ⟨1, by omega⟩
      have huv : u ≠ v := by simp [u, v]
      let F : SimpleGraph (Fin h) := SimpleGraph.edge u v
      have hmF : F.edgeSet.ncard = 1 := by
        dsimp [F]
        rw [SimpleGraph.edge_edgeSet_of_ne huv]
        simp
      have haux := embedding_from_auxiliary G w hw hconn h hh H F 1 hmF (by omega)
        (graphOneSubdiv_has_edgeless_induced_minor H F hHbot) hfree hn
      simpa [hq0] using haux
  · have hcard : Fintype.card V ≤ 1 := by omega
    haveI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hcard
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro u v
      rw [Subsingleton.elim v u, weightedDist_self' hw]
      simp
    · simp only [sub_self, abs_zero, Finset.sum_const_zero, mul_zero]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro u _
      apply Finset.sum_eq_zero
      intro v _
      rw [Subsingleton.elim v u]
      exact weightedDist_self' hw u

private theorem separator_from_auxiliary
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ℕ) (hh : 2 ≤ h)
    (H : SimpleGraph (Fin h)) [DecidableRel H.Adj]
    (F : SimpleGraph (Fin h)) (qF : ℕ)
    (hmF : F.edgeSet.ncard = qF) (hqF : 1 ≤ qF)
    (hFH : HasInducedMinor_internal (graphOneSubdiv F) H)
    (hm : 1 ≤ G.edgeFinset.card)
    (hfree : ¬G.ContainsInducedMinor H) :
    G.HasBalancedSeparator (2 / 3)
      (4 * (45 * Real.sqrt ((h : ℝ) + H.edgeFinset.card) *
        Real.sqrt (G.edgeFinset.card : ℝ) *
        (65536 * Real.log (8 * ((3 * h + qF + 7 : ℕ) : ℝ))))) := by
  let ρ : ℝ := 65536 * Real.log (8 * ((3 * h + qF + 7 : ℕ) : ℝ))
  have hρ : 0 < ρ := by
    dsimp [ρ]
    apply mul_pos (by norm_num)
    apply Real.log_pos
    push_cast
    have hhR : (2 : ℝ) ≤ h := by exact_mod_cast hh
    have hqR : (1 : ℝ) ≤ qF := by exact_mod_cast hqF
    nlinarith
  letI : Nonempty (Fin h) := Fin.pos_iff_nonempty.mp (by omega)
  have hbound : ∀ (S : Finset V), 2 ≤ S.card → S.Nonempty →
      (G.induce (↑S : Set V)).Connected →
      Qspread (G.induce (↑S : Set V)) ≤ ρ * Qbar (G.induce (↑S : Set V)) := by
    intro S hS _ hSconn
    have hn : 2 ≤ Fintype.card {v // v ∈ (↑S : Set V)} := by
      simpa [Fintype.card_coe] using hS
    have hsubfree : ¬(G.induce (↑S : Set V)).ContainsInducedMinor H :=
      induced_minor_free_hereditary G H _ hfree
    have hinternal : ¬HasInducedMinor_internal
        (G.induce (↑S : Set V)) (graphOneSubdiv F) := by
      intro hsubdiv
      apply hsubfree
      have h₁ : HasInducedMinor (G.induce (↑S : Set V)) (graphOneSubdiv F) :=
        internal_to_public_hasInducedMinor hsubdiv
      have h₂ : HasInducedMinor (graphOneSubdiv F) H :=
        internal_to_public_hasInducedMinor hFH
      exact hasInducedMinor_imp_containsInducedMinor
        (SimpleGraph.HasInducedMinor.trans h₁ h₂)
    simpa [ρ] using logarithmic_spread_bound_internal
      (G.induce (↑S : Set V)) hSconn h qF hh hqF F hmF hinternal hn
  have hsep := separator_of_general_spread_bound G H hm hfree ρ hρ hbound
  simpa [ρ] using hsep

/-- **Improved induced-minor separator theorem (positive-edge case).**
For an arbitrary `h`-vertex, `q`-edge forbidden graph `H`, the separator
bound has logarithmic rather than quadratic embedding loss. -/
theorem improved_separator_theorem
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ℕ) (hh : 2 ≤ h)
    (H : SimpleGraph (Fin h)) [DecidableRel H.Adj]
    (hq : 1 ≤ H.edgeFinset.card)
    (hm : 1 ≤ G.edgeFinset.card)
    (hfree : ¬G.ContainsInducedMinor H) :
    G.HasBalancedSeparator (2 / 3)
      (4 * (45 *
        Real.sqrt ((h : ℝ) + H.edgeFinset.card) *
        Real.sqrt (G.edgeFinset.card : ℝ) *
        (65536 * Real.log
          (8 * ((3 * h + H.edgeFinset.card + 7 : ℕ) : ℝ))))) := by
  exact separator_from_auxiliary G h hh H H H.edgeFinset.card
    (edgeSet_ncard_eq_edgeFinset_card H) hq
    (graphOneSubdiv_has_original_induced_minor H) hm hfree

/-- **Improved induced-minor separator theorem.** This version includes the
edgeless forbidden graph case by adjoining one auxiliary edge for the
structural theorem. -/
theorem improved_separator_theorem_all
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ℕ) (hh : 2 ≤ h)
    (H : SimpleGraph (Fin h)) [DecidableRel H.Adj]
    (hm : 1 ≤ G.edgeFinset.card)
    (hfree : ¬G.ContainsInducedMinor H) :
    G.HasBalancedSeparator (2 / 3)
      (4 * (45 * Real.sqrt ((h : ℝ) + H.edgeFinset.card) *
        Real.sqrt (G.edgeFinset.card : ℝ) *
        (65536 * Real.log
          (8 * ((3 * h + max 1 H.edgeFinset.card + 7 : ℕ) : ℝ))))) := by
  by_cases hq : 1 ≤ H.edgeFinset.card
  · simpa [max_eq_right hq] using improved_separator_theorem G h hh H hq hm hfree
  · have hq0 : H.edgeFinset.card = 0 := by omega
    have hHbot : H = ⊥ := by
      apply SimpleGraph.ext
      funext u v
      apply propext
      constructor
      · intro huv
        have he : s(u, v) ∈ H.edgeFinset := by simpa using huv
        rw [Finset.card_eq_zero.mp hq0] at he
        simp at he
      · simp
    let u : Fin h := ⟨0, by omega⟩
    let v : Fin h := ⟨1, by omega⟩
    have huv : u ≠ v := by simp [u, v]
    let F : SimpleGraph (Fin h) := SimpleGraph.edge u v
    have hmF : F.edgeSet.ncard = 1 := by
      dsimp [F]
      rw [SimpleGraph.edge_edgeSet_of_ne huv]
      simp
    have haux := separator_from_auxiliary G h hh H F 1 hmF (by omega)
      (graphOneSubdiv_has_edgeless_induced_minor H F hHbot) hm hfree
    simpa [hq0] using haux

#print axioms improved_embedding_theorem_arbitrary
#print axioms improved_separator_theorem
#print axioms improved_separator_theorem_all

end
