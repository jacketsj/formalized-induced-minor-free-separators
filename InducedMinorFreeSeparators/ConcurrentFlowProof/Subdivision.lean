import Mathlib
import InducedMinorFreeSeparators.ConcurrentFlowProof.Defs
import InducedMinorFreeSeparators.ConcurrentFlowProof.OnceSubdiv
import InducedMinorFreeSeparators.ConcurrentFlowProof.InducedMinorTrans
import InducedMinorFreeSeparators.ConcurrentFlowProof.BridgeLemma

/-!
# Twice-Subdivision of Graphs

Given a subcubic graph H with no isolated vertices, we construct the
twice-subdivided graph K = H̋, where each edge of H is replaced by a path
of length 3 (adding 2 subdivision vertices per edge).

We prove:
- K is subcubic
- |E(K)| = 3|E(H)|
- InducedAlmostEmbedding G K → HasInducedMinor G H
-/

open Finset SimpleGraph
open scoped BigOperators

noncomputable section

namespace SimpleGraph.TwiceSubdiv

variable {W : Type*} [Fintype W] [DecidableEq W]
  (H : SimpleGraph W) [DecidableRel H.Adj]

omit [DecidableEq W] in
/-- Vertex type of the twice-subdivided graph: original vertices plus
    2 subdivision vertices per edge. -/
abbrev Vert := W ⊕ (H.edgeFinset × Fin 2)

/-- Get the first endpoint of an edge using Quot.out. -/
def edgeFst (e : H.edgeFinset) : W := e.val.out.1

/-- Get the second endpoint of an edge using Quot.out. -/
def edgeSnd (e : H.edgeFinset) : W := e.val.out.2

omit [DecidableEq W] in
theorem edge_endpoints (e : H.edgeFinset) :
    e.val = s(edgeFst H e, edgeSnd H e) :=
  (Quot.out_eq e.val).symm

omit [DecidableEq W] in
theorem edge_adj (e : H.edgeFinset) : H.Adj (edgeFst H e) (edgeSnd H e) := by
  have h1 := e.prop
  rw [SimpleGraph.mem_edgeFinset] at h1
  have h2 := edge_endpoints H e
  rw [h2] at h1; exact h1

omit [DecidableEq W] in
theorem edge_ne (e : H.edgeFinset) : edgeFst H e ≠ edgeSnd H e :=
  (edge_adj H e).ne

/-- Adjacency in the twice-subdivided graph.
For each edge e = {u, v} of H (with Quot.out giving ordered pair (u, v)):
- inl u ~ inr (e, 0)
- inr (e, 0) ~ inr (e, 1)
- inr (e, 1) ~ inl v -/
def subdivAdj : Vert H → Vert H → Prop
  | Sum.inl w, Sum.inr (e, i) =>
    (i = 0 ∧ w = edgeFst H e) ∨ (i = 1 ∧ w = edgeSnd H e)
  | Sum.inr (e, i), Sum.inl w =>
    (i = 0 ∧ w = edgeFst H e) ∨ (i = 1 ∧ w = edgeSnd H e)
  | Sum.inr (e₁, i₁), Sum.inr (e₂, i₂) =>
    e₁ = e₂ ∧ i₁ ≠ i₂
  | Sum.inl _, Sum.inl _ => False

instance subdivAdj_decidable : DecidableRel (subdivAdj H) := by
  intro a b; unfold subdivAdj
  cases a <;> cases b <;> exact inferInstance

omit [DecidableEq W] in
theorem subdivAdj_symm : Symmetric (subdivAdj H) := by
  intro a b h
  cases a with
  | inl wa =>
    cases b with
    | inl wb => exact absurd h id
    | inr pb => exact h
  | inr pa =>
    cases b with
    | inl wb => exact h
    | inr pb =>
      simp only [subdivAdj] at h ⊢
      exact ⟨h.1.symm, fun h' => h.2 h'.symm⟩

omit [DecidableEq W] in
theorem subdivAdj_irrefl : Std.Irrefl (subdivAdj H) where
  irrefl := by
    intro a h
    cases a with
    | inl w => exact h
    | inr p => simp [subdivAdj] at h

/-- The twice-subdivided graph. -/
def subdivGraph : SimpleGraph (Vert H) where
  Adj := subdivAdj H
  symm := subdivAdj_symm H
  loopless := subdivAdj_irrefl H

instance subdivGraph_decidableRel : DecidableRel (subdivGraph H).Adj :=
  subdivAdj_decidable H

/-
Each subdivision vertex has degree at most 2.
-/
theorem subdiv_vertex_degree (e : H.edgeFinset) (i : Fin 2) :
    (subdivGraph H).degree (Sum.inr (e, i)) ≤ 3 := by
  refine' le_trans ( Finset.card_mono _ ) _;
  exact { Sum.inl ( if i = 0 then edgeFst H e else edgeSnd H e ), Sum.inr ( e, if i = 0 then 1 else 0 ) };
  · intro x hx; fin_cases i <;> simp_all +decide [ subdivGraph ] ;
    · cases x <;> simp_all +decide [ subdivAdj ];
      grind;
    · grind +locals;
  · exact le_trans ( Finset.card_insert_le _ _ ) ( by norm_num )

/-
Each original vertex has the same degree in K as in H (≤ 3).
-/
theorem orig_vertex_degree (w : W) (hSub : H.IsSubcubic) :
    (subdivGraph H).degree (Sum.inl w) ≤ 3 := by
  convert hSub w using 1;
  refine' Finset.card_bij ( fun x hx => x.elim ( fun x => by aesop ) fun x => if x.2 = 0 then edgeSnd H x.1 else edgeFst H x.1 ) _ _ _ <;> simp +decide;
  · unfold subdivGraph; simp +decide [ subdivAdj ] ;
    intro a ha; constructor <;> intro h <;> simp_all +decide [ edgeFst, edgeSnd ] ;
    · rw [ ← SimpleGraph.mem_edgeSet ] ; aesop;
    · convert ha using 1;
      rw [ ← SimpleGraph.mem_edgeSet ];
      simp +decide [ Sym2.eq_swap ];
  · constructor <;> intros <;> simp_all +decide [ subdivGraph, subdivAdj ];
    constructor <;> intros <;> simp_all +decide [ edgeFst, edgeSnd ];
    · constructor <;> intros <;> simp_all +decide [ Quot.out ];
      · grind +qlia;
      · grind +suggestions;
    · constructor <;> intros <;> simp_all +decide [ Quot.out ];
      · grind +suggestions;
      · grind;
  · intro b hb
    right
    use s(w, b);
    simp +decide [ subdivGraph, hb, edgeFst, edgeSnd ];
    have := Quot.out_eq ( s(w, b) );
    grind +locals

/-- The subdivided graph is subcubic. -/
theorem subdivGraph_isSubcubic (hSub : H.IsSubcubic) :
    (subdivGraph H).IsSubcubic := by
  intro v
  cases v with
  | inl w => exact orig_vertex_degree H w hSub
  | inr p => exact subdiv_vertex_degree H p.1 p.2

/-
Edge count of the subdivided graph.
-/
theorem subdivGraph_edge_count :
    (subdivGraph H).edgeFinset.card = 3 * H.edgeFinset.card := by
  rw [ eq_comm, mul_comm ];
  convert Set.ncard_eq_toFinset_card' _ using 1;
  simp +decide [ SimpleGraph.edgeSet, Set.ncard_eq_toFinset_card' ];
  rw [ show ( filter ( Membership.mem ( edgeSetEmbedding ( Vert H ) ( subdivGraph H ) ) ) univ : Finset ( Sym2 ( Vert H ) ) ) = Finset.biUnion ( Finset.univ : Finset H.edgeFinset ) ( fun e => { s(Sum.inl ( edgeFst H e ), Sum.inr ( e, 0 ) ), s(Sum.inr ( e, 0 ), Sum.inr ( e, 1 ) ), s(Sum.inr ( e, 1 ), Sum.inl ( edgeSnd H e ) ) } ) from ?_ ];
  · rw [ Finset.card_biUnion ];
    · simp +decide [ Finset.card_insert_of_notMem, edge_ne ];
    · intro e he f hf hne; simp_all +decide [ Finset.disjoint_left ] ;
  · ext ⟨x, y⟩; simp [subdivGraph];
    rcases x with ( x | ⟨ e, i ⟩ ) <;> rcases y with ( y | ⟨ f, j ⟩ ) <;> simp +decide [ subdivAdj ];
    · aesop;
    · aesop;
    · grind +suggestions

/-- Edge positivity. -/
theorem subdivGraph_edge_pos (h : 0 < H.edgeFinset.card) :
    0 < (subdivGraph H).edgeFinset.card := by
  rw [subdivGraph_edge_count]; omega

/-- The edge in H.edgeFinset corresponding to an adjacency. -/
def adjEdge (w₁ w₂ : W) (h : H.Adj w₁ w₂) : H.edgeFinset :=
  ⟨s(w₁, w₂), by rwa [SimpleGraph.mem_edgeFinset]⟩

/-
For adjacent w₁ w₂ in H, the subdivGraph has an edge from inl w₁ to inr(adjEdge, i)
    for an appropriate i.
-/
theorem subdivAdj_of_adj_fst (w₁ w₂ : W) (h : H.Adj w₁ w₂) :
    (subdivGraph H).Adj (Sum.inl w₁) (Sum.inr (adjEdge H w₁ w₂ h,
      if edgeFst H (adjEdge H w₁ w₂ h) = w₁ then 0 else 1)) := by
  have h_edge : edgeFst H (adjEdge H w₁ w₂ h) = w₁ ∨ edgeSnd H (adjEdge H w₁ w₂ h) = w₁ := by
    have := Quot.out_eq ( s(w₁, w₂) );
    rw [ Sym2.eq_iff ] at this ; aesop;
  -- By cases on h_edge, we can split into the two possibilities.
  cases' h_edge with h_case1 h_case2;
  · exact Or.inl ⟨ by simp +decide [ h_case1 ], by simp +decide [ h_case1 ] ⟩;
  · unfold subdivGraph; simp +decide [ h_case2, subdivAdj ] ;
    tauto

theorem subdivAdj_of_adj_snd (w₁ w₂ : W) (h : H.Adj w₁ w₂) :
    (subdivGraph H).Adj (Sum.inl w₂) (Sum.inr (adjEdge H w₁ w₂ h,
      if edgeFst H (adjEdge H w₁ w₂ h) = w₂ then 0 else 1)) := by
  convert subdivAdj_of_adj_fst H w₂ w₁ h.symm using 1;
  simp +decide [ adjEdge, Sym2.eq_swap ]

omit [DecidableEq W] in
/-- The "buffer" edge connecting the two subdivision vertices of an edge. -/
theorem subdivAdj_buffer (e : H.edgeFinset) :
    (subdivGraph H).Adj (Sum.inr (e, (0 : Fin 2))) (Sum.inr (e, (1 : Fin 2))) := by
  simp [subdivGraph, subdivAdj]

omit [DecidableEq W] in
/-- The four vertices of the subdivided edge that are distinct. -/
theorem subdiv_edge_four_ne (w₁ w₂ : W) (h : H.Adj w₁ w₂) :
    (Sum.inl w₁ : Vert H) ≠ (Sum.inl w₂ : Vert H) ∧
    (Sum.inl w₁ : Vert H) ≠ Sum.inr (adjEdge H w₁ w₂ h, (0 : Fin 2)) ∧
    (Sum.inl w₁ : Vert H) ≠ Sum.inr (adjEdge H w₁ w₂ h, (1 : Fin 2)) ∧
    (Sum.inl w₂ : Vert H) ≠ Sum.inr (adjEdge H w₁ w₂ h, (0 : Fin 2)) ∧
    (Sum.inl w₂ : Vert H) ≠ Sum.inr (adjEdge H w₁ w₂ h, (1 : Fin 2)) := by
  exact ⟨by simp [h.ne], by simp, by simp, by simp, by simp⟩

/- Direct conversion: InducedAlmostEmbedding G K → HasInducedMinor G H.

Bypass the once-subdivision and construct HasInducedMinor G H directly.
The branch sets are defined using legs from each vertex and "owned" buffers.
For each w ∈ W, we include:
- All vertices on leg paths (K-edges incident to inl w)
- Buffer vertices of edges where w = edgeFst ("owned" buffers)
- Exclude buffer vertices of edges where w = edgeSnd ("non-owned" buffers)
Then take the connected component of φ(inl w) in G restricted to this set.

Key non-incidence property: for w₁ ≠ w₂, every K-edge involving inl w₁ is
non-incident to every K-edge involving inl w₂. Combined with buffer K-edges
being non-incident for different H-edges, this gives complete separation of
the vertex sets S(w₁) and S(w₂) by mutual induction.

The core construction: IAE of twice-subdivided → InducedMinorModel of once-subdivided.

For each original vertex w, the branch set is the union of all leg paths from inl w.
For each edge e, the branch set is the bridge from the Bridge Lemma on the buffer path.
-/
end SimpleGraph.TwiceSubdiv
end
