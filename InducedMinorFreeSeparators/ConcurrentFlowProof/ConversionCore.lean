import Mathlib
import InducedMinorFreeSeparators.ConcurrentFlowProof.Defs
import InducedMinorFreeSeparators.ConcurrentFlowProof.Subdivision
import InducedMinorFreeSeparators.ConcurrentFlowProof.BridgeLemma
import InducedMinorFreeSeparators.ConcurrentFlowProof.BridgeConstruction

/-!
# Core conversion: IAE of twice-subdivision → InducedMinorModel of once-subdivision
-/

open Finset SimpleGraph
open scoped BigOperators

noncomputable section

namespace SimpleGraph.ConvCore

variable {W : Type*} [Fintype W] [DecidableEq W]
  (H : SimpleGraph W) [DecidableRel H.Adj]
  {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (φ : InducedAlmostEmbedding G (TwiceSubdiv.subdivGraph H))

-- Adjacency proofs for the subdivGraph
omit [Nonempty V] [DecidableRel G.Adj] in
private def adj_fst (e : H.edgeFinset) :
    (TwiceSubdiv.subdivGraph H).Adj (Sum.inl (TwiceSubdiv.edgeFst H e)) (Sum.inr (e, (0 : Fin 2))) :=
  Or.inl ⟨rfl, rfl⟩

private def adj_snd (e : H.edgeFinset) :
    (TwiceSubdiv.subdivGraph H).Adj (Sum.inl (TwiceSubdiv.edgeSnd H e)) (Sum.inr (e, (1 : Fin 2))) :=
  Or.inr ⟨rfl, rfl⟩

-- The leg paths
private def legFst (e : H.edgeFinset) : List V :=
  φ.edgeMap (Sum.inl (TwiceSubdiv.edgeFst H e)) (Sum.inr (e, 0)) (adj_fst H e)

private def legSnd (e : H.edgeFinset) : List V :=
  φ.edgeMap (Sum.inl (TwiceSubdiv.edgeSnd H e)) (Sum.inr (e, 1)) (adj_snd H e)

private def buffer (e : H.edgeFinset) : List V :=
  φ.edgeMap (Sum.inr (e, (0 : Fin 2))) (Sum.inr (e, (1 : Fin 2))) (TwiceSubdiv.subdivAdj_buffer H e)

omit [Nonempty V] [DecidableRel G.Adj] in
-- The two legs of each edge are mutually induced
private lemma legs_mi (e : H.edgeFinset) :
    MutuallyInducedPaths G (legFst H G φ e) (legSnd H G φ e) :=
  TwiceSubdiv.leg_paths_mutually_induced φ (TwiceSubdiv.edge_ne H e) (adj_fst H e) (adj_snd H e)

-- buffer properties
omit [Nonempty V] [DecidableRel G.Adj] in
private lemma buffer_valid (e : H.edgeFinset) :
    (buffer H G φ e).IsChain G.Adj ∧ (buffer H G φ e).Nodup ∧ 2 ≤ (buffer H G φ e).length ∧
    (buffer H G φ e).head? = some (φ.vertexMap (Sum.inr (e, (0 : Fin 2)))) ∧
    (buffer H G φ e).getLast? = some (φ.vertexMap (Sum.inr (e, (1 : Fin 2)))) :=
  φ.edgeMap_valid _ _ (TwiceSubdiv.subdivAdj_buffer H e)

-- legFst ends at vertexMap(inr(e,0))
omit [Nonempty V] [DecidableRel G.Adj] in
private lemma legFst_valid (e : H.edgeFinset) :
    (legFst H G φ e).IsChain G.Adj ∧ (legFst H G φ e).Nodup ∧ 2 ≤ (legFst H G φ e).length ∧
    (legFst H G φ e).head? = some (φ.vertexMap (Sum.inl (TwiceSubdiv.edgeFst H e))) ∧
    (legFst H G φ e).getLast? = some (φ.vertexMap (Sum.inr (e, (0 : Fin 2)))) :=
  φ.edgeMap_valid _ _ (adj_fst H e)

-- legSnd ends at vertexMap(inr(e,1))
omit [Nonempty V] [DecidableRel G.Adj] in
private lemma legSnd_valid (e : H.edgeFinset) :
    (legSnd H G φ e).IsChain G.Adj ∧ (legSnd H G φ e).Nodup ∧ 2 ≤ (legSnd H G φ e).length ∧
    (legSnd H G φ e).head? = some (φ.vertexMap (Sum.inl (TwiceSubdiv.edgeSnd H e))) ∧
    (legSnd H G φ e).getLast? = some (φ.vertexMap (Sum.inr (e, (1 : Fin 2)))) :=
  φ.edgeMap_valid _ _ (adj_snd H e)

/-
buffer head is in legFst
omit [Nonempty V] [DecidableRel G.Adj] in
-/
omit [Nonempty V] [DecidableRel G.Adj] in
private lemma buffer_head_in_legFst (e : H.edgeFinset) :
    (buffer H G φ e).get ⟨0, by have := (buffer_valid H G φ e).2.2.1; omega⟩ ∈
    (legFst H G φ e).toFinset := by
  have := legFst_valid H G φ e; have := buffer_valid H G φ e; simp_all +decide ;
  grind +splitIndPred

/-
buffer last is in legSnd
omit [Nonempty V] [DecidableRel G.Adj] in
-/
omit [Nonempty V] [DecidableRel G.Adj] in
private lemma buffer_last_in_legSnd (e : H.edgeFinset) :
    (buffer H G φ e).get ⟨(buffer H G φ e).length - 1, by have := (buffer_valid H G φ e).2.2.1; omega⟩ ∈
    (legSnd H G φ e).toFinset := by
  have := (legSnd_valid H G φ e).2.2.2.2;
  have := (buffer_valid H G φ e).2.2.2.2;
  grind +suggestions

-- The bridge data for each edge
omit [Nonempty V] [DecidableRel G.Adj] in
private lemma bridge_data (e : H.edgeFinset) :
    ∃ S : Set V, Set.Nonempty S ∧
      (∀ v ∈ S, v ∈ ((buffer H G φ e).toFinset : Set V)) ∧
      (∀ v ∈ S, v ∉ (legFst H G φ e).toFinset) ∧
      (∀ v ∈ S, v ∉ (legSnd H G φ e).toFinset) ∧
      (G.induce S).Connected ∧
      (∃ a s, a ∈ (legFst H G φ e).toFinset ∧ s ∈ S ∧ G.Adj a s) ∧
      (∃ b s, b ∈ (legSnd H G φ e).toFinset ∧ s ∈ S ∧ G.Adj s b) := by
  have hbuf := buffer_valid H G φ e
  have hmi := legs_mi H G φ e
  exact BridgeLemma.bridge_exists (buffer H G φ e) hbuf.2.2.1 hbuf.1 hbuf.2.1
    (legFst H G φ e).toFinset (legSnd H G φ e).toFinset
    (buffer_head_in_legFst H G φ e) (buffer_last_in_legSnd H G φ e)
    hmi.1 (fun a ha b hb => hmi.2 a (List.mem_toFinset.mp ha) b (List.mem_toFinset.mp hb))

-- Choose the bridge set
private def bridge (e : H.edgeFinset) : Set V :=
  Classical.choose (bridge_data H G φ e)

omit [Nonempty V] [DecidableRel G.Adj] in
private lemma bridge_nonempty (e : H.edgeFinset) : Set.Nonempty (bridge H G φ e) :=
  (Classical.choose_spec (bridge_data H G φ e)).1

omit [Nonempty V] [DecidableRel G.Adj] in
private lemma bridge_in_buffer (e : H.edgeFinset) :
    ∀ v ∈ bridge H G φ e, v ∈ ((buffer H G φ e).toFinset : Set V) :=
  (Classical.choose_spec (bridge_data H G φ e)).2.1

omit [Nonempty V] [DecidableRel G.Adj] in
private lemma bridge_not_in_legFst (e : H.edgeFinset) :
    ∀ v ∈ bridge H G φ e, v ∉ (legFst H G φ e).toFinset :=
  (Classical.choose_spec (bridge_data H G φ e)).2.2.1

omit [Nonempty V] [DecidableRel G.Adj] in
private lemma bridge_not_in_legSnd (e : H.edgeFinset) :
    ∀ v ∈ bridge H G φ e, v ∉ (legSnd H G φ e).toFinset :=
  (Classical.choose_spec (bridge_data H G φ e)).2.2.2.1

omit [Nonempty V] [DecidableRel G.Adj] in
private lemma bridge_connected (e : H.edgeFinset) :
    (G.induce (bridge H G φ e)).Connected :=
  (Classical.choose_spec (bridge_data H G φ e)).2.2.2.2.1

omit [Nonempty V] [DecidableRel G.Adj] in
private lemma bridge_adj_legFst (e : H.edgeFinset) :
    ∃ a s, a ∈ (legFst H G φ e).toFinset ∧ s ∈ bridge H G φ e ∧ G.Adj a s :=
  (Classical.choose_spec (bridge_data H G φ e)).2.2.2.2.2.1

omit [Nonempty V] [DecidableRel G.Adj] in
private lemma bridge_adj_legSnd (e : H.edgeFinset) :
    ∃ b s, b ∈ (legSnd H G φ e).toFinset ∧ s ∈ bridge H G φ e ∧ G.Adj s b :=
  (Classical.choose_spec (bridge_data H G φ e)).2.2.2.2.2.2

-- Branch set for original vertex w: union of all leg paths
def branchOrig (w : W) : Set V :=
  { v | ∃ (e : H.edgeFinset) (i : Fin 2)
    (h : (TwiceSubdiv.subdivGraph H).Adj (Sum.inl w) (Sum.inr (e, i))),
    v ∈ (φ.edgeMap (Sum.inl w) (Sum.inr (e, i)) h).toFinset }

-- The combined branch function for the once-subdivided graph
def branchFn : OnceSubdiv.Vert H → Set V
  | Sum.inl w => branchOrig H G φ w
  | Sum.inr e => bridge H G φ e

/-
Helper: a chain list with all elements in S gives reachability in G.induce S
-/
omit [Fintype V] [DecidableEq V] [Nonempty V] [DecidableRel G.Adj] in
private lemma chain_reachable_in_superset (l : List V) (hl : l.IsChain G.Adj)
    (S : Set V) (hS : ∀ v ∈ l, v ∈ S) (v : V) (hv : v ∈ l) (hl2 : l ≠ []) :
    (G.induce S).Reachable ⟨l.head hl2, hS _ (List.head_mem hl2)⟩ ⟨v, hS v hv⟩ := by
  induction l <;> simp_all +decide;
  · contradiction;
  · cases hl ; simp_all +decide; all_goals grind +suggestions

/-
Property 1: Connected
omit [Nonempty V] [DecidableRel G.Adj] in
-/
omit [Nonempty V] [DecidableRel G.Adj] in
lemma branch_connected_orig (w : W) (hNoIsol : ∀ v : W, ∃ w : W, H.Adj v w) :
    (G.induce (branchOrig H G φ w)).Connected := by
  -- By hNoIsol, obtain w ' with H.Adj w w'. Get the subdivAdj adjacency: there exists e : H.edgeFinset and i : Fin 2 with hadj : (subdivGraph H).Adj (inl w) (inr(e,i)).
  obtain ⟨w', hw'⟩ := hNoIsol w
  obtain ⟨e, i, hadj⟩ : ∃ e : H.edgeFinset, ∃ i : Fin 2, (TwiceSubdiv.subdivGraph H).Adj (Sum.inl w) (Sum.inr (e, i)) := by
    -- By definition of `subdivGraph`, there exists an edge `e` in `H` such that `w` is adjacent to `e` in `subdivGraph H`.
    use ⟨s(w, w'), by
      aesop⟩
    generalize_proofs at *;
    unfold TwiceSubdiv.subdivGraph; simp +decide ;
    unfold TwiceSubdiv.subdivAdj; simp +decide ;
    unfold TwiceSubdiv.edgeFst TwiceSubdiv.edgeSnd; simp +decide ;
    have := Quot.out_eq ( s(w, w') );
    rw [ Sym2.eq_iff ] at this ; aesop;
  -- Set l₀ := φ.edge Map (inl w) (inr(e,i)) hadj. By edgeMap_valid, l₀.head? = some (φ.vertexMap (inl w)) and l₀ is nonempty (length ≥ 2).
  set l₀ := φ.edgeMap (Sum.inl w) (Sum.inr (e, i)) hadj
  have hl₀_head : l₀.head? = some (φ.vertexMap (Sum.inl w)) := by
    exact φ.edgeMap_valid _ _ _ |>.2.2.2.1
  have hl₀_nonempty : l₀ ≠ [] := by
    grind
  have hl₀_hub : φ.vertexMap (Sum.inl w) ∈ l₀.toFinset := by
    exact List.mem_toFinset.mpr ( List.mem_of_mem_head? hl₀_head );
  -- Use connected_iff_exists_forall_reachable with hub = ⟨φ.vertexMap (inl w), hub_mem⟩.
  have h_hub_mem : φ.vertexMap (Sum.inl w) ∈ branchOrig H G φ w := by
    grind +locals;
  refine' SimpleGraph.connected_iff_exists_forall_reachable _ |>.mpr ⟨ ⟨ _, h_hub_mem ⟩, fun ⟨ v, hv ⟩ => _ ⟩;
  -- Obtain ⟨f, j, hadj', hv'⟩  from hv.
  obtain ⟨f, j, hadj', hv'⟩ := hv;
  -- Set l := φ.edgeMap (inl w) (inr(f,j)) hadj'. By edgeMap_valid, l is a chain, l ≠ [], and l.head? = some (φ.vertexMap (inl w)), so l.head = φ.vertexMap (inl w).
  set l := φ.edgeMap (Sum.inl w) (Sum.inr (f, j)) hadj'
  have hl_chain : l.IsChain G.Adj := by
    exact φ.edgeMap_valid _ _ _ |>.1
  have hl_nonempty : l ≠ [] := by
    exact fun h => by simp +decide [ h ] at hv';
  have hl_head : l.head? = some (φ.vertexMap (Sum.inl w)) := by
    exact φ.edgeMap_valid _ _ _ |>.2.2.2.1
  have hl_hub : φ.vertexMap (Sum.inl w) = l.head hl_nonempty := by
    exact Option.some_inj.mp ( hl_head.symm.trans ( by rw [ List.head?_eq_some_head ] ) );
  have := chain_reachable_in_superset G l hl_chain ( branchOrig H G φ w ) ( fun v hv => by
    exact ⟨ f, j, hadj', by simpa using hv ⟩ ) v ( by
    exact List.mem_toFinset.mp hv' ) hl_nonempty;
  grind

/-
Property 2: Disjoint - original vs original
-/
omit [Nonempty V] [DecidableRel G.Adj] in
lemma branch_disjoint_orig_orig (w₁ w₂ : W) (hne : w₁ ≠ w₂) :
    Disjoint (branchOrig H G φ w₁) (branchOrig H G φ w₂) := by
  have h_disjoint : ∀ (e₁ : H.edgeFinset) (i₁ : Fin 2) (h₁ : (TwiceSubdiv.subdivGraph H).Adj (Sum.inl w₁) (Sum.inr (e₁, i₁))) (e₂ : H.edgeFinset) (i₂ : Fin 2) (h₂ : (TwiceSubdiv.subdivGraph H).Adj (Sum.inl w₂) (Sum.inr (e₂, i₂))), Disjoint (List.toFinset
 (φ.edgeMap (Sum.inl w₁) (Sum.inr (e₁, i₁)) h₁)) (List.toFinset (φ.edgeMap (Sum.inl w₂) (Sum.inr (e₂, i₂)) h₂)) := by
    intro e₁ i₁ h₁ e₂ i₂ h₂;
    have := φ.mutually_induced ( Sum.inl w₁ ) ( Sum.inr ( e₁, i₁ ) ) ( Sum.inl w₂ ) ( Sum.inr ( e₂, i₂ ) ) h₁ h₂;
    cases eq_or_ne ( e₁, i₁ ) ( e₂, i₂ ) <;> simp_all +decide [ MutuallyInducedPaths ];
    cases h₁ ; cases h₂ ; aesop;
    · grind;
    · cases h₂ ; aesop;
      grobner;
  simp_all +decide [ Set.disjoint_left, branchOrig ];
  intro a x hx hx' y hy; specialize h_disjoint x hx; rcases hx' with ( ⟨ h₁, h₂ ⟩ | ⟨ h₁, h₂ ⟩ ) <;> simp_all +decide [ List.disjoint_left ] ;

/-
Property 2: Disjoint - original vs bridge
-/
omit [Nonempty V] [DecidableRel G.Adj] in
lemma branch_disjoint_orig_bridge (w : W) (e : H.edgeFinset) :
    Disjoint (branchOrig H G φ w) (bridge H G φ e) := by
  rw [ Set.disjoint_left ];
  rintro v ⟨ f, i, h, hv ⟩ hv';
  by_cases h_cases : f = e;
  · fin_cases i <;> simp_all +decide [ TwiceSubdiv.subdivGraph ];
    · have h_leg_fst : w = TwiceSubdiv.edgeFst H e := by
        cases h ; aesop;
        grobner;
      exact bridge_not_in_legFst H G φ e v hv' ( by aesop );
    · have h_finset : φ.edgeMap (Sum.inl w) (Sum.inr (e, 1)) (by
      aesop) = legSnd H G φ e := by
        all_goals generalize_proofs at *;
        have h_finset : w = TwiceSubdiv.edgeSnd H e := by
          cases h ; aesop;
          grobner
        generalize_proofs at *;
        aesop
      generalize_proofs at *;
      exact bridge_not_in_legSnd H G φ e v hv' ( h_finset ▸ hv |> fun h => by simpa using h );
  · have h_disjoint : Disjoint (φ.edgeMap (Sum.inl w) (Sum.inr (f, i)) h).toFinset (φ.edgeMap (Sum.inr (e, (0 : Fin 2))) (Sum.inr (e, (1 : Fin 2))) (TwiceSubdiv.subdivAdj_buffer H e)).toFinset := by
      have := φ.mutually_induced ( Sum.inl w ) ( Sum.inr ( f, i ) ) ( Sum.inr ( e, 0 ) ) ( Sum.inr ( e, 1 ) ) ; simp_all +decide [ MutuallyInducedPaths ] ;
    exact Finset.disjoint_left.mp h_disjoint hv ( bridge_in_buffer H G φ e v hv' )

/-
Property 2: Disjoint - bridge vs bridge
-/
omit [Nonempty V] [DecidableRel G.Adj] in
lemma branch_disjoint_bridge_bridge (e₁ e₂ : H.edgeFinset) (hne : e₁ ≠ e₂) :
    Disjoint (bridge H G φ e₁) (bridge H G φ e₂) := by
  have h_disjoint : (buffer H G φ e₁).toFinset ∩ (buffer H G φ e₂).toFinset = ∅ := by
    have := φ.mutually_induced ( Sum.inr ( e₁, 0 ) ) ( Sum.inr ( e₁, 1 ) ) ( Sum.inr ( e₂, 0 ) ) ( Sum.inr ( e₂, 1 ) ) ( TwiceSubdiv.subdivAdj_buffer H e₁ ) ( TwiceSubdiv.subdivAdj_buffer H e₂ ) ; simp_all +decide [ Finset.ext_iff ] ;
    intro a ha hb; have := this.1; simp_all +decide [ Finset.disjoint_left ] ;
    exact this ha hb;
  simp_all +decide [ Finset.ext_iff ];
  exact Set.disjoint_left.mpr fun x hx₁ hx₂ => h_disjoint x ( by simpa using bridge_in_buffer H G φ e₁ x hx₁ ) ( by simpa using bridge_in_buffer H G φ e₂ x hx₂ )

/-
Property 3: Adjacency - (inl w, inr e) when w = edgeFst e
-/
omit [Nonempty V] [DecidableRel G.Adj] in
lemma adj_preserved_fst (e : H.edgeFinset) :
    ∃ u₁ ∈ branchOrig H G φ (TwiceSubdiv.edgeFst H e),
    ∃ u₂ ∈ bridge H G φ e, G.Adj u₁ u₂ := by
  obtain ⟨ a, s, ha, hs, has ⟩ := bridge_adj_legFst H G φ e;
  refine' ⟨ a, _, s, hs, has ⟩;
  exact ⟨ e, 0, adj_fst H e, by simpa using ha ⟩

/-
Property 3: Adjacency - (inl w, inr e) when w = edgeSnd e
-/
omit [Nonempty V] [DecidableRel G.Adj] in
lemma adj_preserved_snd (e : H.edgeFinset) :
    ∃ u₁ ∈ branchOrig H G φ (TwiceSubdiv.edgeSnd H e),
    ∃ u₂ ∈ bridge H G φ e, G.Adj u₁ u₂ := by
  obtain ⟨ b, s, hb, hs, h ⟩ := bridge_adj_legSnd H G φ e;
  refine' ⟨ b, _, s, hs, h.symm ⟩;
  exact ⟨ e, 1, adj_snd H e, by simpa using hb ⟩

/-
Property 4: Non-adjacency - original vs original
-/
omit [Nonempty V] [DecidableRel G.Adj] in
lemma nonadj_orig_orig (w₁ w₂ : W) (hne : w₁ ≠ w₂) :
    ∀ u₁ ∈ branchOrig H G φ w₁, ∀ u₂ ∈ branchOrig H G φ w₂, ¬G.Adj u₁ u₂ := by
  intro u₁ hu₁ u₂ hu₂;
  obtain ⟨e₁, i₁, h₁, hu₁⟩ := hu₁
  obtain ⟨e₂, i₂, h₂, hu₂⟩ := hu₂;
  have := SimpleGraph.TwiceSubdiv.leg_paths_mutually_induced φ hne h₁ h₂; simp_all +decide [ MutuallyInducedPaths ] ;

/-
Property 4: Non-adjacency - original vs bridge when not endpoint
-/
omit [Nonempty V] [DecidableRel G.Adj] in
lemma nonadj_orig_bridge (w : W) (e : H.edgeFinset)
    (hw1 : w ≠ TwiceSubdiv.edgeFst H e) (hw2 : w ≠ TwiceSubdiv.edgeSnd H e) :
    ∀ u₁ ∈ branchOrig H G φ w, ∀ u₂ ∈ bridge H G φ e, ¬G.Adj u₁ u₂ := by
  intro u₁ hu₁ u₂ hu₂ h_adj
  obtain ⟨f, j, hfj, hu₁'⟩ := hu₁
  have h_f_ne_e : f ≠ e := by
    cases hfj <;> aesop;
  have := φ.mutually_induced ( Sum.inl w ) ( Sum.inr ( f, j ) ) ( Sum.inr ( e, 0 ) ) ( Sum.inr ( e, 1 ) ) hfj ( TwiceSubdiv.subdivAdj_buffer H e ) ; simp_all +decide [ MutuallyInducedPaths ] ;
  exact this.2 u₁ hu₁' u₂ ( by simpa using bridge_in_buffer H G φ e u₂ hu₂ ) h_adj

/-
Property 4: Non-adjacency - bridge vs bridge
-/
omit [Nonempty V] [DecidableRel G.Adj] in
lemma nonadj_bridge_bridge (e₁ e₂ : H.edgeFinset) (hne : e₁ ≠ e₂) :
    ∀ u₁ ∈ bridge H G φ e₁, ∀ u₂ ∈ bridge H G φ e₂, ¬G.Adj u₁ u₂ := by
  intros u₁ hu₁ u₂ hu₂
  have h_buffer : u₁ ∈ (buffer H G φ e₁).toFinset ∧ u₂ ∈ (buffer H G φ e₂).toFinset := by
    exact ⟨ by simpa using bridge_in_buffer H G φ e₁ u₁ hu₁, by simpa using bridge_in_buffer H G φ e₂ u₂ hu₂ ⟩;
  have := φ.mutually_induced ( Sum.inr ( e₁, 0 ) ) ( Sum.inr ( e₁, 1 ) ) ( Sum.inr ( e₂, 0 ) ) ( Sum.inr ( e₂, 1 ) ) ?_ ?_ <;> simp_all +decide [ MutuallyInducedPaths ];
  all_goals norm_num [ TwiceSubdiv.subdivGraph, TwiceSubdiv.subdivAdj ];
  exact this.2 _ h_buffer.1 _ h_buffer.2

/-
Main theorem assembling the InducedMinorModel
-/
omit [Nonempty V] [DecidableRel G.Adj] in
theorem iae_to_once_subdiv_core
    (_hSub : H.IsSubcubic) (hNoIsol : ∀ v : W, ∃ w : W, H.Adj v w)
    (_ : φ = φ) -- force φ into scope
    :
    HasInducedMinor G (OnceSubdiv.onceSubdivGraph H) := by
  refine ⟨{ branch := branchFn H G φ, branch_connected := ?_, branch_disjoint := ?_,
            adj_preserved := ?_, nonadj_preserved := ?_ }⟩
  · -- Connected
    intro v; cases v with
    | inl w => exact branch_connected_orig H G φ w hNoIsol
    | inr e => exact bridge_connected H G φ e
  · -- Disjoint
    intro v₁ v₂ hne
    cases v₁ with
    | inl w₁ => cases v₂ with
      | inl w₂ => exact branch_disjoint_orig_orig H G φ w₁ w₂ (by aesop)
      | inr e₂ => exact branch_disjoint_orig_bridge H G φ w₁ e₂
    | inr e₁ => cases v₂ with
      | inl w₂ => exact (branch_disjoint_orig_bridge H G φ w₂ e₁).symm
      | inr e₂ => exact branch_disjoint_bridge_bridge H G φ e₁ e₂ (by aesop)
  · -- Adjacency
    intro v₁ v₂ hadj
    cases v₁ with
    | inl w₁ => cases v₂ with
      | inl w₂ => simp [OnceSubdiv.onceSubdivGraph, OnceSubdiv.onceSubdivAdj] at hadj
      | inr e₂ =>
        simp [OnceSubdiv.onceSubdivGraph, OnceSubdiv.onceSubdivAdj] at hadj
        cases hadj with
        | inl h => subst h; exact adj_preserved_fst H G φ e₂
        | inr h => subst h; exact adj_preserved_snd H G φ e₂
    | inr e₁ => cases v₂ with
      | inl w₂ =>
        simp [OnceSubdiv.onceSubdivGraph, OnceSubdiv.onceSubdivAdj] at hadj
        cases hadj with
        | inl h =>
          subst h; obtain ⟨a, ha, s, hs, hadj⟩ := adj_preserved_fst H G φ e₁
          exact ⟨s, hs, a, ha, hadj.symm⟩
        | inr h =>
          subst h; obtain ⟨a, ha, s, hs, hadj⟩ := adj_preserved_snd H G φ e₁
          exact ⟨s, hs, a, ha, hadj.symm⟩
      | inr e₂ => simp [OnceSubdiv.onceSubdivGraph, OnceSubdiv.onceSubdivAdj] at hadj
  · -- Non-adjacency
    intro w₁ w₂ hne hne' v₁ hv₁ v₂ hv₂;
    cases w₁ <;> cases w₂ <;> simp_all +decide [ OnceSubdiv.onceSubdivGraph ];
    · exact nonadj_orig_orig H G φ _ _ hne _ hv₁ _ hv₂;
    · contrapose! hne';
      rename_i w e;
      have := nonadj_orig_bridge H G φ w e;
      exact Classical.not_not.1 fun h => this ( by rintro rfl; exact h ( Or.inl rfl ) ) ( by rintro rfl; exact h ( Or.inr rfl ) ) v₁ hv₁ v₂ hv₂ hne';
    · unfold branchFn at hv₁ hv₂;
      unfold OnceSubdiv.onceSubdivAdj at hne' ; simp_all +decide;
      exact fun h => nonadj_orig_bridge H G φ _ _ hne'.1 hne'.2 _ hv₂ _ hv₁ h.symm;
    · exact nonadj_bridge_bridge H G φ _ _ hne _ hv₁ _ hv₂

end SimpleGraph.ConvCore

namespace SimpleGraph.TwiceSubdiv

variable {W : Type*} [Fintype W] [DecidableEq W]
  (H : SimpleGraph W) [DecidableRel H.Adj]

theorem direct_conversion
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hSub : H.IsSubcubic) (hNoIsol : ∀ v : W, ∃ w : W, H.Adj v w)
    (φ : InducedAlmostEmbedding G (subdivGraph H)) :
    HasInducedMinor G H :=
  HasInducedMinor.trans
    (ConvCore.iae_to_once_subdiv_core H G φ hSub hNoIsol rfl)
    (OnceSubdiv.hasInducedMinor_of_onceSubdiv H)

theorem conversion
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hSub : H.IsSubcubic) (hNoIsol : ∀ v : W, ∃ w : W, H.Adj v w) :
    Nonempty (InducedAlmostEmbedding G (subdivGraph H)) → HasInducedMinor G H := by
  intro ⟨φ⟩
  exact direct_conversion H G hSub hNoIsol φ

/-- Main theorem: universe bridge to Type 0. -/
theorem exists_subdiv_impl
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hSub : H.IsSubcubic) (hNoIsol : ∀ v : W, ∃ w : W, H.Adj v w) :
    ∃ (W' : Type) (_ : Fintype W') (_ : DecidableEq W'),
    ∃ (K : SimpleGraph W') (_ : DecidableRel K.Adj),
      K.IsSubcubic ∧
      K.edgeFinset.card = 3 * H.edgeFinset.card ∧
      (0 < H.edgeFinset.card → 0 < K.edgeFinset.card) ∧
      (Nonempty (InducedAlmostEmbedding G K) → HasInducedMinor G H) := by
  set n := Fintype.card (TwiceSubdiv.Vert H)
  set e := Fintype.equivFin (TwiceSubdiv.Vert H)
  set K := (subdivGraph H).comap e.symm
  let iso : (subdivGraph H) ≃g K :=
    { toEquiv := e
      map_rel_iff' := by intro a b; simp [K, SimpleGraph.comap_adj] }
  refine ⟨Fin n, inferInstance, inferInstance, K, inferInstance, ?_, ?_, ?_, ?_⟩
  · intro v
    have hkey : iso (e.symm v) = v := by show e (e.symm v) = v; simp
    rw [← hkey, iso.degree_eq]
    exact subdivGraph_isSubcubic H hSub (e.symm v)
  · rw [← iso.card_edgeFinset_eq]
    exact subdivGraph_edge_count H
  · intro h
    rw [← iso.card_edgeFinset_eq]
    exact subdivGraph_edge_pos H h
  · intro ⟨ae⟩
    exact conversion H G hSub hNoIsol ⟨{
      vertexMap := fun w => ae.vertexMap (iso w)
      edgeMap := fun w₁ w₂ h => ae.edgeMap (iso w₁) (iso w₂) (iso.map_rel_iff.mpr h)
      edgeMap_valid := fun w₁ w₂ h => ae.edgeMap_valid (iso w₁) (iso w₂) (iso.map_rel_iff.mpr h)
      mutually_induced := fun w₁ w₂ w₃ w₄ h₁ h₂ hne₁ hne₂ hne₃ hne₄ =>
        ae.mutually_induced (iso w₁) (iso w₂) (iso w₃) (iso w₄)
          (iso.map_rel_iff.mpr h₁) (iso.map_rel_iff.mpr h₂)
          (fun h => hne₁ (iso.injective h)) (fun h => hne₂ (iso.injective h))
          (fun h => hne₃ (iso.injective h)) (fun h => hne₄ (iso.injective h))
    }⟩

end SimpleGraph.TwiceSubdiv
end
