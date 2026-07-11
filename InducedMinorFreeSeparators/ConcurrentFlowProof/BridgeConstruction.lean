import Mathlib
import InducedMinorFreeSeparators.ConcurrentFlowProof.Defs
import InducedMinorFreeSeparators.ConcurrentFlowProof.Subdivision

/-!
# Bridge Construction Helpers

Helper lemmas for the direct conversion from InducedAlmostEmbedding to HasInducedMinor.
-/

open Finset SimpleGraph
open scoped BigOperators

noncomputable section

namespace SimpleGraph.TwiceSubdiv

variable {W : Type*} [Fintype W] [DecidableEq W]
  {H : SimpleGraph W} [DecidableRel H.Adj]
  {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-
Two K-edges incident to different original vertices are non-incident
(share no K-vertex), so their paths are MutuallyInducedPaths.
-/
omit [Nonempty V] [DecidableRel G.Adj] in
omit [Nonempty V] [DecidableRel G.Adj] in
theorem leg_paths_mutually_induced
    (φ : InducedAlmostEmbedding G (subdivGraph H))
    {w₁ w₂ : W} (hw : w₁ ≠ w₂)
    {e₁ : H.edgeFinset} {i₁ : Fin 2}
    {e₂ : H.edgeFinset} {i₂ : Fin 2}
    (h₁ : (subdivGraph H).Adj (Sum.inl w₁) (Sum.inr (e₁, i₁)))
    (h₂ : (subdivGraph H).Adj (Sum.inl w₂) (Sum.inr (e₂, i₂))) :
    MutuallyInducedPaths G
      (φ.edgeMap (Sum.inl w₁) (Sum.inr (e₁, i₁)) h₁)
      (φ.edgeMap (Sum.inl w₂) (Sum.inr (e₂, i₂)) h₂) := by
  convert φ.mutually_induced ( Sum.inl w₁ ) ( Sum.inr ( e₁, i₁ ) ) ( Sum.inl w₂ ) ( Sum.inr ( e₂, i₂ ) ) h₁ h₂ _ _ _ _ using 1 <;> simp +decide [ hw ];
  cases h₁ ; cases h₂ ; aesop;
  · grind +ring;
  · cases h₂ ; aesop;
    aesop

/-
φ(inl w₁) and φ(inl w₂) are distinct for w₁ ≠ w₂,
when both vertices have incident edges.
omit [Nonempty V] [DecidableRel G.Adj] in
-/
omit [Nonempty V] [DecidableRel G.Adj] in
theorem vertexMap_injective_of_noIsol
    (φ : InducedAlmostEmbedding G (subdivGraph H))
    {w₁ w₂ : W} (hw : w₁ ≠ w₂)
    (hNoIsol : ∀ v : W, ∃ w : W, H.Adj v w) :
    φ.vertexMap (Sum.inl w₁) ≠ φ.vertexMap (Sum.inl w₂) := by
  -- Since w₁ has a neighbor (h NoIsol), get edge e₁ incident to w₁ and the corresponding K-edge.  Similarly for w₂.
  obtain ⟨e₁, he₁⟩ := hNoIsol w₁
  obtain ⟨e₂, he₂⟩ := hNoIsol w₂;
  -- By leg_paths_mutually_induced, the two leg paths are MutuallyInducedPaths, meaning they are vertex-disjoint (Disjoint on toFinset).
  have h_disjoint : Disjoint (φ.edgeMap (Sum.inl w₁) (Sum.inr (adjEdge H w₁ e₁ he₁, if edgeFst H (adjEdge H w₁ e₁ he₁) = w₁ then 0 else 1)) (subdivAdj_of_adj_fst H w₁ e₁ he₁)).toFinset (φ.edgeMap (Sum.inl w₂) (Sum.inr (adjEdge H w₂ e₂ he₂, if edgeFst H (adjEdge H w₂ e₂ he₂) = w₂ then 0 else 1)) (subdivAdj_of_adj_fst H w₂ e₂ he₂)).toFinset := by
    apply (leg_paths_mutually_induced φ hw (subdivAdj_of_adj_fst H w₁ e₁ he₁) (subdivAdj_of_adj_fst H w₂ e₂ he₂)).left;
  have := φ.edgeMap_valid ( Sum.inl w₁ ) ( Sum.inr ( adjEdge H w₁ e₁ he₁, if edgeFst H ( adjEdge H w₁ e₁ he₁ ) = w₁ then 0 else 1 ) ) ( subdivAdj_of_adj_fst H w₁ e₁ he₁ ) ; have := φ.edgeMap_valid ( Sum.inl w₂ ) ( Sum.inr ( adjEdge H w₂ e₂ he₂, if edgeFst H ( adjEdge H w₂ e₂ he₂ ) = w₂ then 0 else 1 ) ) ( subdivAdj_of_adj_fst H w₂ e₂ he₂ ) ; simp_all +decide ;
  cases h : φ.edgeMap ( Sum.inl w₁ ) ( Sum.inr ( adjEdge H w₁ e₁ he₁, if edgeFst H ( adjEdge H w₁ e₁ he₁ ) = w₁ then 0 else 1 ) ) ( subdivAdj_of_adj_fst H w₁ e₁ he₁ ) <;> cases h' : φ.edgeMap ( Sum.inl w₂ ) ( Sum.inr ( adjEdge H w₂ e₂ he₂, if edgeFst H (
 adjEdge H w₂ e₂ he₂ ) = w₂ then 0 else 1 ) ) ( subdivAdj_of_adj_fst H w₂ e₂ he₂ ) <;> simp_all +decide [ List.disjoint_iff_ne ]

/-
For non-adjacent w₁, w₂ in H, φ(inl w₁) and φ(inl w₂) are not G-adjacent.
-/
omit [Nonempty V] [DecidableRel G.Adj] in
theorem vertexMap_nonadj
    (φ : InducedAlmostEmbedding G (subdivGraph H))
    {w₁ w₂ : W} (hw : w₁ ≠ w₂) (_hnadj : ¬H.Adj w₁ w₂)
    (hNoIsol : ∀ v : W, ∃ w : W, H.Adj v w) :
    ¬G.Adj (φ.vertexMap (Sum.inl w₁)) (φ.vertexMap (Sum.inl w₂)) := by
  obtain ⟨ v₁, hv₁ ⟩ := hNoIsol w₁
  obtain ⟨ v₂, hv₂ ⟩ := hNoIsol w₂

  have h₁ := subdivAdj_of_adj_fst H w₁ v₁ hv₁
  have h₂ := subdivAdj_of_adj_fst H w₂ v₂ hv₂

  have h₃ := leg_paths_mutually_induced φ hw h₁ h₂

  have h₄ := h₃.2 (φ.vertexMap (Sum.inl w₁)) (by
  have := φ.edgeMap_valid ( Sum.inl w₁ ) ( Sum.inr ( adjEdge H w₁ v₁ hv₁, if edgeFst H ( adjEdge H w₁ v₁ hv₁ ) = w₁ then 0 else 1 ) ) h₁; simp_all +decide ;
  exact List.mem_of_mem_head? this.2.2.2.1) (φ.vertexMap (Sum.inl w₂)) (by
  have := φ.edgeMap_valid ( Sum.inl w₂ ) ( Sum.inr ( adjEdge H w₂ v₂ hv₂, if edgeFst H ( adjEdge H w₂ v₂ hv₂ ) = w₂ then 0 else 1 ) ) h₂;
  exact List.mem_of_mem_head? this.2.2.2.1)

  exact h₄

end SimpleGraph.TwiceSubdiv
end
