import Mathlib
import InducedMinorFreeSeparators.ConcurrentFlowProof.Defs

open Finset SimpleGraph
open scoped BigOperators NNReal

noncomputable section

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-
A concurrent flow on G implies G is connected.
-/
lemma ConcurrentFlow.connected (cf : ConcurrentFlow G) : G.Connected := by
  refine' ⟨ _ ⟩;
  by_cases h : ∃ s t : V, s ≠ t ∧ ¬G.Reachable s t;
  · obtain ⟨ s, t, hst, h ⟩ := h; have := cf.total_flow s t hst; simp_all +decide ;
    contrapose! this;
    rw [ Finset.sum_eq_zero ] <;> simp_all +decide;
    intro l hl hs ht; have := cf.valid l hl; simp_all +decide [ List.isChain_iff_getElem ] ;
    have h_walk : ∀ i : Fin l.length, G.Reachable s (l.get i) := by
      intro i; induction' i with i hi; simp_all +decide ;
      induction' i with i ih;
      · cases l <;> aesop;
      · exact SimpleGraph.Reachable.trans ( ih ( Nat.lt_of_succ_lt hi ) ) ( SimpleGraph.Adj.reachable ( this.1 i (by omega) ) );
    convert h_walk ⟨ l.length - 1, Nat.sub_lt ( by linarith ) zero_lt_one ⟩ |> fun h => h.trans ( SimpleGraph.Reachable.refl _ ) using 1;
    grind;
  · exact fun s t => if hst : s = t then hst.symm ▸ SimpleGraph.Reachable.refl _ else by push_neg at h; exact h s t hst;

/-
A connected graph on n ≥ 2 vertices has at least n-1 edges.
-/
omit [DecidableEq V] [Nonempty V] in
lemma Connected.edge_count (hG : G.Connected) (_hV : 2 ≤ Fintype.card V) :
    Fintype.card V - 1 ≤ G.edgeFinset.card := by
      obtain ⟨ T, hT ⟩ := hG.exists_isTree_le;
      have := hT.2.card_edgeFinset; simp_all +decide ;
      exact this ▸ Nat.succ_le_succ ( Finset.card_mono ( by aesop ) )

/-- A concurrent flow implies the graph has at least |V|-1 edges. -/
lemma ConcurrentFlow.edge_count (cf : ConcurrentFlow G) (hV : 2 ≤ Fintype.card V) :
    Fintype.card V - 1 ≤ G.edgeFinset.card :=
  cf.connected.edge_count hV

end SimpleGraph
end
