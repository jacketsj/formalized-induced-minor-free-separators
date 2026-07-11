import Mathlib
import InducedMinorFreeSeparators.ConcurrentFlowProof.Defs

/-!
# Once-Subdivision and H as Induced Minor

We define the once-subdivided graph Ḣ and show that H is an induced minor
of Ḣ (by contracting subdivision vertices into their neighbors).
-/

open Finset SimpleGraph
open scoped BigOperators

noncomputable section

namespace SimpleGraph.OnceSubdiv

variable {W : Type*} [Fintype W] [DecidableEq W]
  (H : SimpleGraph W) [DecidableRel H.Adj]

/-- Vertex type of the once-subdivided graph. -/
abbrev Vert := W ⊕ H.edgeFinset

/-- Get the first endpoint of an edge using Quot.out. -/
def edgeFst (e : H.edgeFinset) : W := e.val.out.1

/-- Get the second endpoint of an edge using Quot.out. -/
def edgeSnd (e : H.edgeFinset) : W := e.val.out.2

/-- Adjacency: inl w ~ inr e iff w is an endpoint of e. No inl-inl or inr-inr edges. -/
def onceSubdivAdj : Vert H → Vert H → Prop
  | Sum.inl w, Sum.inr e => w = edgeFst H e ∨ w = edgeSnd H e
  | Sum.inr e, Sum.inl w => w = edgeFst H e ∨ w = edgeSnd H e
  | _, _ => False

instance : DecidableRel (onceSubdivAdj H) := by
  intro a b; unfold onceSubdivAdj; cases a <;> cases b <;> exact inferInstance

omit [DecidableEq W] in
theorem onceSubdivAdj_symm : Symmetric (onceSubdivAdj H) := by
  intro a b h; cases a <;> cases b <;> exact h

omit [DecidableEq W] in
theorem onceSubdivAdj_irrefl : Std.Irrefl (onceSubdivAdj H) where
  irrefl := by intro a h; cases a <;> simp [onceSubdivAdj] at h

omit [DecidableEq W] in
omit [DecidableEq W] in
/-- The once-subdivided graph. -/
def onceSubdivGraph : SimpleGraph (Vert H) where
  Adj := onceSubdivAdj H
  symm := onceSubdivAdj_symm H
  loopless := onceSubdivAdj_irrefl H

instance onceSubdivGraph_decidableRel : DecidableRel (onceSubdivGraph H).Adj := by
  intro a b; simp only [onceSubdivGraph]; exact inferInstance

/-
H is an induced minor of its once-subdivision.
Branch set for w: {inl w} ∪ {inr e | edgeFst e = w}
(we assign each subdivision vertex to the "first" endpoint of its edge).
-/
omit [DecidableEq W] in
theorem hasInducedMinor_of_onceSubdiv :
    HasInducedMinor (onceSubdivGraph H) H := by
  constructor;
  constructor;
  case branch => exact fun w => { Sum.inl w } ∪ { v | ∃ e : H.edgeFinset, v = Sum.inr e ∧ edgeFst H e = w };
  · intro w;
    refine' SimpleGraph.connected_iff_exists_forall_reachable _ |>.2 ⟨ ⟨ Sum.inl w, _ ⟩, _ ⟩ <;> simp +decide [ SimpleGraph.Reachable ];
    constructor;
    · rintro a rfl; exact ⟨ SimpleGraph.Walk.nil ⟩ ;
    · rintro a ha b hb rfl hq; use SimpleGraph.Walk.cons ( by
        exact Or.inl ( by aesop ) ) SimpleGraph.Walk.nil;
  · simp +contextual [ Set.disjoint_left ];
    aesop;
  · intro w₁ w₂ hadj
    obtain ⟨e, he⟩ : ∃ e : H.edgeFinset, edgeFst H e = w₁ ∧ edgeSnd H e = w₂ ∨ edgeFst H e = w₂ ∧ edgeSnd H e = w₁ := by
      have := Quot.out_eq ( s(w₁, w₂) : Sym2 W );
      rw [ Sym2.eq_iff ] at this ; aesop;
    cases' he with he he <;> [ refine' ⟨ _, Or.inr ⟨ e, rfl, he.1 ⟩, _, Or.inl rfl, _ ⟩ ; refine' ⟨ _, Or.inl rfl, _, Or.inr ⟨ e, rfl, he.1 ⟩, _ ⟩ ] <;> simp +decide [ *, onceSubdivGraph ];
    · exact Or.inr ( by aesop );
    · exact Or.inr he.2.symm;
  · simp +decide [ onceSubdivGraph ];
    unfold onceSubdivAdj; simp +decide [ edgeFst, edgeSnd ] ;
    grind +suggestions

end SimpleGraph.OnceSubdiv
end
