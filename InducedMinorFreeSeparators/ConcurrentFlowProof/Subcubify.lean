import Mathlib
import InducedMinorFreeSeparators.ConcurrentFlowProof.Defs

/-!
# Subcubification of graphs

We prove `SimpleGraph.exists_subcubify_noIsol`: for any finite simple graph H,
there exists a subcubic graph H'' with no isolated vertices containing H as
an induced minor, with |E(H'')| ≤ 3·(|V(H)| + |E(H)|).
-/

open Finset SimpleGraph
open scoped BigOperators

noncomputable section

universe u

namespace SimpleGraph.Subcubify

variable {W : Type u} [Fintype W] [DecidableEq W]
  (H : SimpleGraph W) [DecidableRel H.Adj]

omit [DecidableEq W] in
/-- The number of vertices in the replacement tree for vertex w. -/
def treeSize (w : W) : ℕ :=
  if H.degree w = 0 then 2
  else if H.degree w ≤ 3 then 1
  else H.degree w - 2

omit [DecidableEq W] in
theorem treeSize_pos (w : W) : 0 < treeSize H w := by
  simp only [treeSize]; split_ifs <;> omega

/-- The vertex type of the subcubified graph. -/
abbrev Vert := Σ (w : W), Fin (treeSize H w)

/-- A bijection between the neighbor finset of w and Fin (H.degree w). -/
def neighborEnum (w : W) : H.neighborFinset w ≃ Fin (H.degree w) :=
  (H.neighborFinset w).equivFin

/-- Given H.Adj w₁ w₂, the port index of w₂ among w₁'s neighbors. -/
def portIndex (w₁ w₂ : W) (h : H.Adj w₁ w₂) : Fin (H.degree w₁) :=
  neighborEnum H w₁ ⟨w₂, by rwa [H.mem_neighborFinset]⟩

/-- Map a port index to the tree node that handles it.
For degree ≤ 3: single node (index 0).
For degree d ≥ 4 with k = d-2 nodes:
- Ports 0,1 → node 0
- Ports 2..k → nodes 1..k-1
- Port k+1 → node k-1 -/
def portToNode (w : W) (p : Fin (H.degree w)) : Fin (treeSize H w) := by
  simp only [treeSize]
  split_ifs with h1 h2
  · exact absurd p.pos (by omega)
  · exact ⟨0, by omega⟩
  · push_neg at h2
    have hp := p.isLt
    exact if hp1 : p.val ≤ 1 then ⟨0, by omega⟩
      else if hp2 : p.val ≤ H.degree w - 2 then ⟨p.val - 1, by omega⟩
      else ⟨H.degree w - 3, by omega⟩

/-- The adjacency relation on the subcubified graph. -/
def subcubAdj : Vert H → Vert H → Prop := fun v₁ v₂ =>
  -- Tree/pendant edge within same vertex
  (v₁.1 = v₂.1 ∧
    ((H.degree v₁.1 = 0 ∧ v₁.2.val + v₂.2.val = 1) ∨
     (H.degree v₁.1 ≥ 1 ∧ (v₁.2.val + 1 = v₂.2.val ∨ v₂.2.val + 1 = v₁.2.val)))) ∨
  -- Cross-tree edge between different vertices
  (v₁.1 ≠ v₂.1 ∧ ∃ (h : H.Adj v₁.1 v₂.1),
    v₁.2 = portToNode H v₁.1 (portIndex H v₁.1 v₂.1 h) ∧
    v₂.2 = portToNode H v₂.1 (portIndex H v₂.1 v₁.1 h.symm))

instance subcubAdj_decidable : DecidableRel (subcubAdj H) := by
  intro v₁ v₂; simp only [subcubAdj]; exact inferInstance

omit [DecidableEq W] in
theorem subcubAdj_symm : Symmetric (subcubAdj H) := by
  intro ⟨w₁, i₁⟩ ⟨w₂, i₂⟩ h
  simp only [subcubAdj] at h ⊢
  rcases h with ⟨heq, h3⟩ | ⟨hne, hadj, h3, h4⟩
  · left; subst heq
    exact ⟨rfl, by rcases h3 with ⟨hd, hp⟩ | ⟨hd, hp⟩ <;> [left; right] <;> exact ⟨hd, by omega⟩⟩
  · right; exact ⟨hne.symm, hadj.symm, h4, h3⟩

omit [DecidableEq W] in
theorem subcubAdj_irrefl : Std.Irrefl (subcubAdj H) where
  irrefl := fun ⟨w, i⟩ h => by
    simp only [subcubAdj] at h
    rcases h with ⟨_, h3⟩ | ⟨hne, _⟩
    · rcases h3 with ⟨_, hp⟩ | ⟨_, hp⟩ <;> omega
    · exact hne rfl

omit [DecidableEq W] in
omit [DecidableEq W] in
/-- The subcubified graph. -/
def subcubGraph : SimpleGraph (Vert H) where
  Adj := subcubAdj H
  symm := subcubAdj_symm H
  loopless := subcubAdj_irrefl H

instance : DecidableRel (subcubGraph H).Adj := subcubAdj_decidable H

/-
Characterization of portToNode values.
-/
omit [DecidableEq W] in
theorem portToNode_val (w : W) (p : Fin (H.degree w)) :
    (portToNode H w p).val =
      if H.degree w ≤ 3 then 0
      else if p.val ≤ 1 then 0
      else if p.val ≤ H.degree w - 2 then p.val - 1
      else H.degree w - 3 := by
  unfold portToNode; split_ifs <;> simp_all +decide ;
  · grind;
  · split_ifs <;> simp +decide [ * ]; all_goals grind +locals

/-
portToNode is injective on ports mapping to interior nodes.
-/
omit [DecidableEq W] in
theorem portToNode_preimage_le (w : W) (i : Fin (treeSize H w)) :
    (Finset.univ.filter (fun p : Fin (H.degree w) => portToNode H w p = i)).card ≤
      if treeSize H w = 1 then 3 else 2 := by
  split_ifs with h;
  · -- Since treeSize H w = 1, we have H.degree w ≤ 3.
    have h_deg : H.degree w ≤ 3 := by
      unfold treeSize at h; split_ifs at h <;> omega;
    exact le_trans ( Finset.card_le_univ _ ) ( by norm_num; linarith );
  · by_cases hw : H.degree w ≤ 3;
    · simp_all +decide [ treeSize ];
      convert Nat.le_of_lt_succ ( show Finset.card ( Finset.univ.filter fun p : Fin ( H.degree w ) => portToNode H w p = i ) < 3 by exact lt_of_le_of_lt ( Finset.card_le_univ _ ) ( by simp +decide [ h ] ) ) using 1;
    · -- Since $H.degree w > 3$,  we have $treeSize H w = H.degree w - 2$.
      have h_treeSize : treeSize H w = H.degree w - 2 := by
        grind +locals;
      -- For $i.val = 0$, the preimage of $i$ under $portToNode$ is $\{0, 1\}$.
      by_cases hi0 : i.val = 0;
      · have h_preimage_zero : Finset.filter (fun p : Fin (H.degree w) => portToNode H w p = i) Finset.univ ⊆ {⟨0, by omega⟩, ⟨1, by omega⟩} := by
          intro p hp; simp_all +decide [ Fin.ext_iff, portToNode ] ;
          grind;
        exact le_trans ( Finset.card_le_card h_preimage_zero ) ( Finset.card_insert_le _ _ );
      · -- For $0 < i.val < degree-3$, the preimage of $i$ under $portToNode$ is $\{i+1\}$.
        by_cases hi1 : i.val < H.degree w - 3;
        · refine' le_trans ( Finset.card_le_one.mpr _ ) _ <;> simp_all +decide;
          grind +suggestions;
        · -- For $i.val = degree-3$, the preimage of $i$ under $portToNode$ is $\{degree-2, degree-1\}$.
          have h_preimage : Finset.filter (fun p : Fin (H.degree w) => portToNode H w p = i) Finset.univ ⊆ {⟨H.degree w - 2, by omega⟩, ⟨H.degree w - 1, by omega⟩} := by
            intro p hp
            simp [] at hp;
            grind +suggestions;
          exact le_trans ( Finset.card_le_card h_preimage ) ( Finset.card_insert_le _ _ )

/-
Tree neighbors (same first component) have at most 2 elements.
-/
theorem tree_neighbors_le (w : W) (i : Fin (treeSize H w)) :
    (Finset.univ.filter (fun j : Fin (treeSize H w) => j ≠ i ∧
      subcubAdj H ⟨w, i⟩ ⟨w, j⟩)).card ≤ 2 := by
  have h_neighbors : ∀ j : Fin (treeSize H w), j ≠ i → subcubAdj H ⟨w, i⟩ ⟨w, j⟩ → j.val = i.val + 1 ∨ j.val = i.val - 1 := by
    unfold subcubAdj;
    grind;
  have h_card : (Finset.univ.filter fun j : Fin (treeSize H w) => j ≠ i ∧ subcubAdj H ⟨w, i⟩ ⟨w, j⟩) ⊆ {⟨if i.val + 1 < treeSize H w then i.val + 1 else i.val, by
    split_ifs <;> linarith [ Fin.is_lt i ]⟩, ⟨if i.val > 0 then i.val - 1 else i.val, by
    grind⟩} := by
    grind;
  exact le_trans ( Finset.card_le_card h_card ) ( Finset.card_insert_le _ _ )

/-
For interior nodes (0 < i < treeSize-1) with degree ≥ 4, at most 1 port maps to them.
-/
omit [DecidableEq W] in
theorem portToNode_preimage_interior (w : W) (i : Fin (treeSize H w))
    (_hts : treeSize H w ≥ 2) (hi0 : 0 < i.val) (hi1 : i.val + 1 < treeSize H w) :
    (Finset.univ.filter (fun p : Fin (H.degree w) => portToNode H w p = i)).card ≤ 1 := by
  have h_port_def : ∀ p : Fin (H.degree w), portToNode H w p = i → p.val = i.val + 1 := by
    intro p hp
    have h_port_def : (portToNode H w p).val = i.val := by
      exact congr_arg Fin.val hp;
    rw [ portToNode_val ] at h_port_def;
    grind +locals;
  exact Finset.card_le_one.mpr fun p hp q hq => Fin.ext <| h_port_def p ( Finset.mem_filter.mp hp |>.2 ) ▸ h_port_def q ( Finset.mem_filter.mp hq |>.2 ) ▸ rfl

/-
Each node has at most 3 neighbors in total (tree + cross-tree).
-/
theorem subcubGraph_degree_le (v : Vert H) : (subcubGraph H).degree v ≤ 3 := by
  obtain ⟨w, i⟩ := v;
  have h_cross_tree_count : (Finset.univ.filter (fun u : Vert H => u.1 ≠ w ∧ subcubAdj H ⟨w, i⟩ u)).card ≤ (Finset.univ.filter (fun p : Fin (H.degree w) => portToNode H w p = i)).card := by
    have h_cross_tree_count : (Finset.univ.filter (fun u : Vert H => u.1 ≠ w ∧ subcubAdj H ⟨w, i⟩ u)).card ≤ (Finset.image (fun u : Vert H => u.1) (Finset.univ.filter (fun u : Vert H => u.1 ≠ w ∧ subcubAdj H ⟨w, i⟩ u))).card := by
      rw [ Finset.card_image_of_injOn ];
      intro u hu v hv; simp_all +decide [ subcubAdj ] ;
      grind;
    refine' le_trans h_cross_tree_count ( le_trans ( Finset.card_le_card _ ) _ );
    exact Finset.image ( fun p : Fin ( H.degree w ) => ( neighborEnum H w ).symm p ) ( Finset.filter ( fun p : Fin ( H.degree w ) => portToNode H w p = i ) Finset.univ );
    · intro u hu; simp_all +decide ;
      grind +locals;
    · exact Finset.card_image_le;
  have h_total_count : (Finset.univ.filter (fun u : Vert H => subcubAdj H ⟨w, i⟩ u)).card ≤ (Finset.univ.filter (fun j : Fin (treeSize H w) => j ≠ i ∧ subcubAdj H ⟨w, i⟩ ⟨w, j⟩)).card + (Finset.univ.filter (fun p : Fin (H.degree w) => portToNode H w p = i)).card := by
    have h_total_count : (Finset.univ.filter (fun u : Vert H => subcubAdj H ⟨w, i⟩ u)).card ≤ (Finset.univ.filter (fun u : Vert H => u.1 = w ∧ subcubAdj H ⟨w, i⟩ u)).card + (Finset.univ.filter (fun u : Vert H => u.1 ≠ w ∧ subcubAdj H ⟨w, i⟩ u)).card := by
      rw [ ← Finset.card_union_of_disjoint ];
      · exact Finset.card_le_card fun x hx => by by_cases h : x.1 = w <;> aesop;
      · exact Finset.disjoint_filter.mpr ( by aesop );
    refine' le_trans h_total_count ( add_le_add _ h_cross_tree_count );
    rw [ show ( Finset.univ.filter fun u : Vert H => u.fst = w ∧ subcubAdj H ⟨ w, i ⟩ u ) = Finset.image ( fun j : Fin ( treeSize H w ) => ⟨ w, j ⟩ ) ( Finset.univ.filter fun j : Fin ( treeSize H w ) => j ≠ i ∧ subcubAdj H ⟨ w, i ⟩ ⟨ w, j ⟩ ) from ?_ ];
    · exact Finset.card_image_le;
    · ext ⟨w', j⟩; simp [subcubAdj];
      grind;
  by_cases hts : treeSize H w = 1;
  · convert h_total_count.trans _;
    · exact congr_arg Finset.card ( by ext; simp +decide [ subcubGraph ] );
    · rw [ Finset.card_eq_zero.mpr ] <;> simp +decide;
      · exact le_trans ( portToNode_preimage_le H w i ) ( by simp +decide [ hts ] );
      · grind;
  · by_cases h_interior : 0 < i.val ∧ i.val + 1 < treeSize H w;
    · convert h_total_count.trans _;
      · exact congr_arg Finset.card ( by ext; simp +decide [ subcubGraph ] );
      · exact le_trans ( add_le_add ( tree_neighbors_le H w i ) ( portToNode_preimage_interior H w i ( by omega ) h_interior.1 h_interior.2 ) ) ( by omega );
    · have h_tree_count : (Finset.univ.filter (fun j : Fin (treeSize H w) => j ≠ i ∧ subcubAdj H ⟨w, i⟩ ⟨w, j⟩)).card ≤ 1 := by
        have h_tree_count : ∀ j : Fin (treeSize H w), j ≠ i → subcubAdj H ⟨w, i⟩ ⟨w, j⟩ → j.val = if i.val = 0 then 1 else i.val - 1 := by
          grind +locals;
        exact Finset.card_le_one.mpr fun x hx y hy => Fin.ext <| by aesop;
      convert h_total_count.trans ( add_le_add h_tree_count ( portToNode_preimage_le H w i ) ) using 1;
      · exact congr_arg Finset.card ( by ext; simp +decide [ subcubGraph ] );
      · grind

/-- The subcubified graph is subcubic. -/
theorem subcubGraph_isSubcubic : (subcubGraph H).IsSubcubic :=
  subcubGraph_degree_le H

/-- Branch set for each vertex of H. -/
def branchSet (w : W) : Set (Vert H) := {v | v.1 = w}

omit [DecidableEq W] in
theorem branchSet_connected (w : W) :
    ((subcubGraph H).induce (branchSet H w)).Connected := by
  simp +decide [ branchSet, SimpleGraph.connected_iff_exists_forall_reachable ];
  refine' ⟨ w, ⟨ 0, _ ⟩, rfl, _ ⟩;
  exact treeSize_pos H w;
  intro a ha
  induction' a with a ha ih;
  induction' ‹Fin ( treeSize H a ) › with i ih;
  induction' i with i ih;
  · aesop;
  · rename_i h;
    refine' ( h ( Nat.lt_of_succ_lt ih ) ha ).trans _;
    refine' SimpleGraph.Adj.reachable _;
    simp +decide [ subcubGraph, subcubAdj ];
    grind +locals

omit [DecidableEq W] in
theorem branchSet_disjoint (w₁ w₂ : W) (h : w₁ ≠ w₂) :
    Disjoint (branchSet H w₁) (branchSet H w₂) := by
  simp [branchSet, Set.disjoint_left]; intro v hv₁ hv₂; exact h (hv₁.symm.trans hv₂)

omit [DecidableEq W] in
theorem branchSet_adj (w₁ w₂ : W) (hadj : H.Adj w₁ w₂) :
    ∃ v₁ ∈ branchSet H w₁, ∃ v₂ ∈ branchSet H w₂, (subcubGraph H).Adj v₁ v₂ := by
  use ⟨w₁, portToNode H w₁ (portIndex H w₁ w₂ hadj)⟩, by
    exact Set.mem_preimage.mp rfl, ⟨w₂, portToNode H w₂ (portIndex H w₂ w₁ hadj.symm)⟩, by
    exact Set.mem_preimage.mp rfl, by
    exact Or.inr ⟨ hadj.ne, hadj, rfl, rfl ⟩

omit [DecidableEq W] in
theorem branchSet_nonadj (w₁ w₂ : W) (hne : w₁ ≠ w₂) (hnadj : ¬H.Adj w₁ w₂)
    (v₁ : Vert H) (hv₁ : v₁ ∈ branchSet H w₁)
    (v₂ : Vert H) (hv₂ : v₂ ∈ branchSet H w₂) :
    ¬(subcubGraph H).Adj v₁ v₂ := by
  -- Since $v₁.1 = w₁$ and $v₂.1 = w₂$, and $w₁ \neq w₂$, the first part of the disjunction in `subcubAdj` is false.
  simp [branchSet] at hv₁ hv₂;
  unfold subcubGraph; simp +decide [  ] ;
  unfold subcubAdj; aesop;

set_option maxHeartbeats 400000 in
def subcubMinorModel : InducedMinorModel (subcubGraph H) H where
  branch := branchSet H
  branch_connected := branchSet_connected H
  branch_disjoint := branchSet_disjoint H
  adj_preserved := branchSet_adj H
  nonadj_preserved := branchSet_nonadj H

theorem subcubGraph_edge_bound :
    (subcubGraph H).edgeFinset.card ≤ 3 * (Fintype.card W + H.edgeFinset.card) := by
  have h_card : (subcubGraph H).edgeFinset.card ≤ 3 * (Fintype.card (Vert H)) / 2 := by
    have h_card : (subcubGraph H).edgeFinset.card ≤ (Fintype.card (Vert H)) * 3 / 2 := by
      have h_sum_degrees : ∑ v : Vert H, (subcubGraph H).degree v ≤ 3 * Fintype.card (Vert H) := by
        exact le_trans ( Finset.sum_le_sum fun _ _ => subcubGraph_degree_le H _ ) ( by simp +decide [ mul_comm ] )
      rw [ Nat.le_div_iff_mul_le ] <;> linarith [ SimpleGraph.sum_degrees_eq_twice_card_edges ( subcubGraph H ) ];
    rwa [ mul_comm ];
  refine' le_trans h_card ( Nat.div_le_of_le_mul _ );
  simp +decide [ Vert, Fintype.card_sigma ];
  -- By definition of ` treeSize`, we know that `treeSize H w  ≤ 2 + H.degree w` for all `w`.
  have h_treeSize_le : ∀ w : W, treeSize H w ≤ 2 + H.degree w := by
    intro w; unfold treeSize; split_ifs <;> omega;
  refine' le_trans ( mul_le_mul_of_nonneg_left ( Finset.sum_le_sum fun w _ => h_treeSize_le w ) zero_le_three ) _;
  simp +decide [ Finset.sum_add_distrib, mul_add , mul_assoc, mul_comm, mul_left_comm, SimpleGraph.sum_degrees_eq_twice_card_edges ]

omit [DecidableEq W] in
theorem subcubGraph_no_isolated :
    ∀ v : Vert H, ∃ w : Vert H, (subcubGraph H).Adj v w := by
  -- For any vertex v = ⟨ w, i⟩, we need to find a neighbor w such that v and w are adjacent in subcubGraph H.
  intro v
  by_cases hw : H.degree v.1 = 0;
  · use ⟨v.1, ⟨1 - v.2.val, by
      grind +locals⟩⟩
    generalize_proofs at *;
    unfold subcubGraph;
    grind +locals;
  · by_cases h : v.2.val + 1 < treeSize H v.1 ∨ v.2.val > 0;
    · refine' ⟨ ⟨ v.1, ⟨ if v.2.val + 1 < treeSize H v.1 then v.2.val + 1 else v.2.val - 1, _ ⟩ ⟩, _ ⟩ <;> simp_all +decide [ subcubGraph ];
      iterate 2 grind +locals;
    · -- Since $v$ is a port node,  there exists an edge in $H$ connecting $v.1$ to some $w'$.
      obtain ⟨w', hw'⟩ : ∃ w', H.Adj v.1 w' := by
        contrapose! hw; simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ] ;
      generalize_proofs at *; simp_all +decide [ Vert ] ;
      refine' ⟨ w', portToNode H w' ( portIndex H w' v.fst hw'.symm ), Or.inr ⟨ _, _ ⟩ ⟩ <;> simp_all +decide;
      · exact hw'.ne;
      · grind +suggestions

theorem subcubGraph_edge_pos
    (h : 0 < Fintype.card W + H.edgeFinset.card) :
    0 < (subcubGraph H).edgeFinset.card := by
  -- Since the graph is nonempty, there must be at least one vertex, and by subcub Graph_no_isolated, there's  an edge incident to that vertex. Therefore, the edgeFinset is nonempty, hence positive.
  have h_nonempty : ∃ v : Vert H, ∃ w : Vert H, (subcubGraph H).Adj v w := by
    have := subcubGraph_no_isolated H;
    by_cases hW : Nonempty W;
    · exact Exists.elim ( this ⟨ hW.some, ⟨ 0, treeSize_pos H hW.some ⟩ ⟩ ) fun w hw => ⟨ _, _, hw ⟩;
    · simp_all +decide;
      exact h ( Subsingleton.elim _ _ );
  grind +suggestions

/-- The main subcubification theorem (universe-polymorphic). -/
theorem exists_subcubify_noIsol_impl :
    ∃ (W'' : Type) (_ : Fintype W'') (_ : DecidableEq W''),
    ∃ (H'' : SimpleGraph W'') (_ : DecidableRel H''.Adj),
      H''.IsSubcubic ∧
      HasInducedMinor H'' H ∧
      H''.edgeFinset.card ≤ 3 * (Fintype.card W + H.edgeFinset.card) ∧
      (∀ v : W'', ∃ w : W'', H''.Adj v w) ∧
      (0 < Fintype.card W + H.edgeFinset.card → 0 < H''.edgeFinset.card) := by
  set n := Fintype.card (Vert H)
  set e := Fintype.equivFin (Vert H)
  set G' := (subcubGraph H).comap e.symm with hG'_def
  let iso : (subcubGraph H) ≃g G' :=
    { toEquiv := e
      map_rel_iff' := by
        intro a b
        simp only [hG'_def, SimpleGraph.comap_adj, Equiv.symm_apply_apply] }
  refine ⟨Fin n, inferInstance, inferInstance, G', inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · -- IsSubcubic
    intro v
    have h1 := subcubGraph_degree_le H (e.symm v)
    have key : iso (e.symm v) = v := by
      change iso.toEquiv (e.symm v) = v
      simp [show iso.toEquiv = e from rfl]
    rw [← key]
    exact (SimpleGraph.Iso.degree_eq iso (e.symm v)).symm ▸ h1
  · -- HasInducedMinor
    exact ⟨(subcubMinorModel H).mapIso iso⟩
  · -- Edge bound
    rw [← iso.card_edgeFinset_eq]
    exact subcubGraph_edge_bound H
  · -- No isolated vertices
    intro v
    obtain ⟨w, hw⟩ := subcubGraph_no_isolated H (e.symm v)
    refine ⟨iso w, ?_⟩
    have key : iso (e.symm v) = v := by
      change iso.toEquiv (e.symm v) = v
      simp [show iso.toEquiv = e from rfl]
    rw [← key]
    exact iso.map_rel_iff.mpr hw
  · -- Edge positivity
    intro h
    rw [← iso.card_edgeFinset_eq]
    exact subcubGraph_edge_pos H h

end SimpleGraph.Subcubify
end
