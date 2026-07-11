/-
# Coarse Pure Pairs

Formalization of Section 4 from the paper: Lemma 4.1 (pure pairs in pseudometric spaces),
Theorem 4.2 (fat models from pseudometric spaces), and Theorem 4.3 (induced minors of
1-subdivisions).

This file is self-contained (apart from the `InducedMinor` import which defines the
internal induced minor model definitions).
-/
import Mathlib

open Set Function
open scoped Classical

noncomputable section

/-! ## Outer Measure (finite version) -/

/-- A finite outer measure on a type V: a monotone, subadditive set function with μ(∅) = 0. -/
structure FinOuterMeasure (V : Type*) where
  toFun : Set V → ℝ
  empty : toFun ∅ = 0
  mono : ∀ {X Y : Set V}, X ⊆ Y → toFun X ≤ toFun Y
  union_le : ∀ (X Y : Set V), toFun (X ∪ Y) ≤ toFun X + toFun Y

instance : CoeFun (FinOuterMeasure V) (fun _ => Set V → ℝ) :=
  ⟨FinOuterMeasure.toFun⟩

@[simp]
theorem FinOuterMeasure.coe_apply (μ : FinOuterMeasure V) (S : Set V) :
    μ.toFun S = μ S := rfl

theorem FinOuterMeasure.nonneg (μ : FinOuterMeasure V) (S : Set V) : 0 ≤ μ S := by
  have h := μ.mono (empty_subset S)
  rw [μ.empty] at h; exact h

theorem FinOuterMeasure.diff_le (μ : FinOuterMeasure V) (X Y : Set V) :
    μ X ≤ μ (X \ Y) + μ Y := by
  calc μ X ≤ μ ((X \ Y) ∪ Y) := μ.mono (fun x hx => by
        by_cases hy : x ∈ Y
        · exact Or.inr hy
        · exact Or.inl ⟨hx, hy⟩)
    _ ≤ μ (X \ Y) + μ Y := μ.union_le _ _

/-- Scale an outer measure by dividing by a positive constant. -/
def FinOuterMeasure.scale (μ : FinOuterMeasure V) (c : ℝ) (hc : 0 < c) :
    FinOuterMeasure V where
  toFun S := μ S / c
  empty := by simp [μ.empty]
  mono h := div_le_div_of_nonneg_right (μ.mono h) (le_of_lt hc)
  union_le X Y := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (μ.union_le X Y) (le_of_lt hc)

/-! ## Metric Balls around Sets -/

/-- B(X, r) = {y | ∃ x ∈ X, dist x y ≤ r} -/
def setBall [PseudoMetricSpace V] (X : Set V) (r : ℝ) : Set V :=
  {y | ∃ x ∈ X, dist x y ≤ r}

theorem setBall_empty [PseudoMetricSpace V] (r : ℝ) : setBall (∅ : Set V) r = ∅ := by
  ext y; simp [setBall]

theorem setBall_singleton [PseudoMetricSpace V] (x : V) (r : ℝ) :
    setBall ({x} : Set V) r = Metric.closedBall x r := by
  ext y; simp [setBall, Metric.mem_closedBall, dist_comm]

theorem setBall_mono_set [PseudoMetricSpace V] {X Y : Set V} (h : X ⊆ Y) (r : ℝ) :
    setBall X r ⊆ setBall Y r :=
  fun _ ⟨x, hx, hd⟩ => ⟨x, h hx, hd⟩

theorem setBall_mono_radius [PseudoMetricSpace V] (X : Set V) {r s : ℝ} (h : r ≤ s) :
    setBall X r ⊆ setBall X s :=
  fun _ ⟨x, hx, hd⟩ => ⟨x, hx, le_trans hd h⟩

theorem self_subset_setBall [PseudoMetricSpace V] (X : Set V) {r : ℝ} (hr : 0 ≤ r) :
    X ⊆ setBall X r :=
  fun x hx => ⟨x, hx, by simp [hr]⟩

theorem setBall_union [PseudoMetricSpace V] (X Y : Set V) (r : ℝ) :
    setBall (X ∪ Y) r = setBall X r ∪ setBall Y r := by
  ext y; simp only [setBall, Set.mem_setOf_eq, Set.mem_union]; constructor
  · rintro ⟨z, hz | hz, hd⟩ <;> [left; right] <;> exact ⟨z, hz, hd⟩
  · rintro (⟨z, hz, hd⟩ | ⟨z, hz, hd⟩)
    · exact ⟨z, Or.inl hz, hd⟩
    · exact ⟨z, Or.inr hz, hd⟩

theorem setBall_iUnion [PseudoMetricSpace V] {ι : Type*} (f : ι → Set V) (r : ℝ) :
    setBall (⋃ i, f i) r = ⋃ i, setBall (f i) r := by
  ext y; simp [setBall]; constructor
  · rintro ⟨z, ⟨i, hi⟩, hd⟩; exact ⟨i, z, hi, hd⟩
  · rintro ⟨i, z, hi, hd⟩; exact ⟨z, ⟨i, hi⟩, hd⟩

/-! ## The Graph Γ_δ and δ-connectivity -/

/-- The graph Γ_δ: vertices at distance ≤ δ are adjacent. -/
def gammaGraph (V : Type*) [PseudoMetricSpace V] (δ : ℝ) : SimpleGraph V where
  Adj x y := x ≠ y ∧ dist x y ≤ δ
  symm x y h := ⟨h.1.symm, by rw [dist_comm]; exact h.2⟩
  loopless := ⟨fun x h => h.1 rfl⟩

/-- A chain relation: a and b are both in X and at distance ≤ δ. -/
def chainRel [PseudoMetricSpace V] (X : Set V) (δ : ℝ) (a b : V) : Prop :=
  a ∈ X ∧ b ∈ X ∧ dist a b ≤ δ

/-- X is δ-connected if X is nonempty and any two points in X are connected by a chain
    of points in X with consecutive distances ≤ δ. -/
def deltaConnected [PseudoMetricSpace V] (δ : ℝ) (X : Set V) : Prop :=
  X.Nonempty ∧ ∀ x ∈ X, ∀ y ∈ X,
    Relation.ReflTransGen (chainRel X δ) x y

/-- Two points are in the same δ-component of X. -/
def sameComponent [PseudoMetricSpace V] (δ : ℝ) (X : Set V) (x y : V) : Prop :=
  x ∈ X ∧ y ∈ X ∧ Relation.ReflTransGen (chainRel X δ) x y

/-- The δ-component of X containing x. -/
def deltaComponent [PseudoMetricSpace V] (δ : ℝ) (X : Set V) (x : V) : Set V :=
  {y ∈ X | Relation.ReflTransGen (chainRel X δ) x y}

/-! ## Connected subsets of a graph -/

/-- A set S is connected in graph G if S is nonempty and any two points in S
    are connected by a path through S using edges of G. -/
def graphSetConnected {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  S.Nonempty ∧ ∀ x ∈ S, ∀ y ∈ S,
    Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ G.Adj a b) x y

/-- Bridge lemma: graphSetConnected implies the induced subgraph is connected. -/
theorem graphSetConnected_to_induce_connected {V : Type*} (G : SimpleGraph V) (S : Set V)
    (h : graphSetConnected G S) : (G.induce S).Connected := by
  obtain ⟨⟨x, hx⟩, hconn⟩ := h
  haveI : Nonempty S := ⟨⟨x, hx⟩⟩
  apply SimpleGraph.Connected.mk
  intro ⟨a, ha⟩ ⟨b, hb⟩
  suffices ∀ c (hc : c ∈ S), Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ G.Adj a b) a c →
      (G.induce S).Reachable ⟨a, ha⟩ ⟨c, hc⟩ from this b hb (hconn a ha b hb)
  intro c hc hchain
  induction hchain with
  | refl => exact ⟨.nil⟩
  | tail _ hbc ih =>
    obtain ⟨hb', hc', hadj⟩ := hbc
    exact (ih hb').trans ⟨SimpleGraph.Walk.cons (SimpleGraph.induce_adj.mpr hadj) .nil⟩

/-! ## Internal induced minor model (for proof machinery) -/

/-- Internal induced minor model structure (used by the fat model construction). -/
structure InducedMinorModel_internal {V : Type*} {W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) where
  branch : W → Set V
  branch_connected : ∀ w, (G.induce (branch w)).Connected
  branch_disjoint : ∀ w₁ w₂, w₁ ≠ w₂ → Disjoint (branch w₁) (branch w₂)
  adj_preserved : ∀ w₁ w₂, H.Adj w₁ w₂ →
    ∃ v₁ ∈ branch w₁, ∃ v₂ ∈ branch w₂, G.Adj v₁ v₂
  nonadj_preserved : ∀ w₁ w₂, w₁ ≠ w₂ → ¬H.Adj w₁ w₂ →
    ∀ v₁ ∈ branch w₁, ∀ v₂ ∈ branch w₂, ¬G.Adj v₁ v₂

def HasInducedMinor_internal {V : Type*} {W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  Nonempty (InducedMinorModel_internal G H)

/-! ## Fat Model -/

/-- A δ-fat model of a graph H in a graph G (with pseudometric on G's vertices).
    Maps vertices and edges of H to connected subsets of G with distance/intersection
    conditions. -/
structure FatModel {V W : Type*} [PseudoMetricSpace W]
    (H : SimpleGraph V) (G : SimpleGraph W) (δ : ℝ) where
  vertexMap : V → Set W
  edgeMap : H.edgeSet → Set W
  vertex_connected : ∀ v, graphSetConnected G (vertexMap v)
  edge_connected : ∀ e, graphSetConnected G (edgeMap e)
  incident_intersect : ∀ (v : V) (e : H.edgeSet), v ∈ e.val →
    (vertexMap v ∩ edgeMap e).Nonempty
  vertex_vertex_far : ∀ v w, v ≠ w →
    ∀ a ∈ vertexMap v, ∀ b ∈ vertexMap w, δ < dist a b
  edge_edge_far : ∀ (e f : H.edgeSet), e ≠ f →
    ∀ a ∈ edgeMap e, ∀ b ∈ edgeMap f, δ < dist a b
  nonincident_far : ∀ (v : V) (e : H.edgeSet), v ∉ e.val →
    ∀ a ∈ vertexMap v, ∀ b ∈ edgeMap e, δ < dist a b

/-! ## 1-Subdivision -/

/-- The 1-subdivision of a graph H (internal version). Vertices are V ⊕ H.edgeSet.
    Each edge e = {u,v} of H is replaced by edges {u, e} and {v, e}. -/
def graphOneSubdiv {V : Type*} (H : SimpleGraph V) :
    SimpleGraph (V ⊕ H.edgeSet) where
  Adj
    | Sum.inl v, Sum.inr ⟨e, _⟩ => v ∈ e
    | Sum.inr ⟨e, _⟩, Sum.inl v => v ∈ e
    | _, _ => False
  symm x y := by
    cases x with
    | inl v => cases y with
      | inl w => simp
      | inr e => exact id
    | inr e => cases y with
      | inl v => exact id
      | inr f => simp

namespace CoarsePurePairs

variable {V : Type*} [Fintype V] [PseudoMetricSpace V]

/-! ## Fin-indexed function extension helpers -/

omit [Fintype V] in
/-- Extend a function on Fin n to Fin (n+1) by adding X at index n. -/
def finExtend (f : Fin n → Set V) (X : Set V) : Fin (n + 1) → Set V :=
  fun i => if h : i.val < n then f ⟨i.val, h⟩ else X

omit [Fintype V] [PseudoMetricSpace V] in
@[simp]
theorem finExtend_last (f : Fin n → Set V) (X : Set V) :
    finExtend f X ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ = X := by
  simp [finExtend]

omit [Fintype V] [PseudoMetricSpace V] in
@[simp]
theorem finExtend_castSucc (f : Fin n → Set V) (X : Set V) (i : Fin n) :
    finExtend f X ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = f i := by
  simp [finExtend, i.isLt]

omit [Fintype V] [PseudoMetricSpace V] in
theorem iUnion_finExtend (f : Fin n → Set V) (X : Set V) :
    (⋃ i, finExtend f X i) = (⋃ i, f i) ∪ X := by
  ext x; simp only [Set.mem_iUnion, Set.mem_union, finExtend]
  constructor
  · rintro ⟨i, hi⟩
    split_ifs at hi with h
    · exact Or.inl ⟨⟨i.val, h⟩, hi⟩
    · exact Or.inr hi
  · rintro (⟨i, hi⟩ | hx)
    · exact ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, by simp [i.isLt, hi]⟩
    · exact ⟨⟨n, Nat.lt_succ_iff.mpr le_rfl⟩, by simp [hx]⟩

omit [Fintype V] [PseudoMetricSpace V] in
theorem iInter_finExtend (f : Fin n → Set V) (X : Set V) :
    (⋂ i, finExtend f X i) = (⋂ i, f i) ∩ X := by
  ext x; simp only [Set.mem_iInter, Set.mem_inter_iff, finExtend]
  constructor
  · intro h
    constructor
    · intro i
      have := h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      simp [i.isLt] at this
      exact this
    · have := h ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩
      simp at this
      exact this
  · rintro ⟨hf, hx⟩ i
    by_cases hi : i.val < n
    · simp [hi]; exact hf ⟨i.val, hi⟩
    · simp [hi]; exact hx

/-! ## Distance between old sets and the new set X ⊆ C -/

omit [Fintype V] in
theorem dist_old_new_gt {ρ δ : ℝ} {f : Fin n → Set V} {X C : Set V}
    (hXC : X ⊆ C) (hC_def : C ⊆ (⋂ i, setBall (f i) (ρ + δ)) \ setBall (⋃ i, f i) ρ)
    (_hρ : 0 ≤ ρ) (_hδ : 0 ≤ δ)
    (j : Fin n) (a : V) (ha : a ∈ f j) (b : V) (hb : b ∈ X) : ρ < dist a b := by
  exact not_le.mp fun h => hC_def ( hXC hb ) |>.2 ⟨ a, Set.mem_iUnion_of_mem j ha, h ⟩

/-! ## Measure bound for the inductive step -/

omit [Fintype V] in
theorem measure_bound_step (μ : FinOuterMeasure V) (C : Set V) (X Y : Set V)
    (ρ δ : ℝ) :
    μ ((C ∩ setBall X (ρ + δ)) \ setBall X ρ) ≥ μ C - μ (setBall X ρ ∪ Y) - μ (C \ (setBall X (ρ + δ) ∪ Y)) := by
  have h_measure_bound : μ.toFun C ≤ μ.toFun ((C ∩ setBall X (ρ + δ)) \ setBall X ρ) + μ.toFun (setBall X ρ ∪ Y) + μ.toFun (C \ (
setBall X (ρ + δ) ∪ Y)) := by
    have h_union : C ⊆ ((C ∩ setBall X (ρ + δ)) \ setBall X ρ) ∪ (setBall X ρ ∪ Y) ∪ (C \ (setBall X (ρ + δ) ∪ Y)) := by
      grind +splitImp
    refine' le_trans ( μ.mono h_union ) _;
    exact le_trans ( μ.union_le _ _ ) ( add_le_add ( μ.union_le _ _ ) le_rfl );
  linarith

/-! ## Greedy selection of far-apart points -/

omit [Fintype V] in
theorem greedy_far_points
    (μ : FinOuterMeasure V) (C : Set V) (r η : ℝ) (hη : 0 ≤ η)
    (h_ball : ∀ x : V, μ (setBall {x} r) ≤ η) :
    ∀ k : ℕ, μ C > (k - 1 : ℝ) * η →
    ∃ (pts : Fin k → V), (∀ i, pts i ∈ C) ∧
      (∀ i j, i ≠ j → r < dist (pts i) (pts j)) := by
  intro k hk;
  induction' k with k ih generalizing C;
  · simp +zetaDelta at *;
  · obtain ⟨c₀, hc₀⟩ : ∃ c₀ ∈ C, True := by
      contrapose! hk;
      rw [ show C = ∅ by ext; aesop ] ; simp +decide [ μ.empty ] ; nlinarith;
    set C' := C \ setBall {c₀} r with hC'
    have hC'_measure : μ.toFun C' ≥ μ.toFun C - μ.toFun (setBall {c₀} r) := by
      have := μ.diff_le C ( setBall { c₀ } r ) ; aesop;
    obtain ⟨pts', hpts'⟩ : ∃ pts' : Fin k → V, (∀ i, pts' i ∈ C') ∧ ∀ i j, i ≠ j → r < dist (pts' i) (pts' j) := by
      apply ih C';
      grind +extAll;
    refine' ⟨ Fin.cons c₀ pts', _, _ ⟩ <;> simp_all +decide [ Fin.forall_fin_succ ];
    simp_all +decide [ dist_comm, setBall ]

/-! ## ReflTransGen chain decomposition -/

private lemma exit_helper {α : Type*} {R : α → α → Prop} {S : Set α} {b : α}
    (hb : b ∉ S) {a : α} (htrans : Relation.TransGen R a b) (ha : a ∈ S) :
    ∃ x y, R x y ∧ x ∈ S ∧ y ∉ S ∧
      Relation.ReflTransGen (fun p q => R p q ∧ p ∈ S ∧ q ∈ S) a x := by
  revert ha
  exact htrans.head_induction_on
    (motive := fun a _ => a ∈ S → ∃ x y, R x y ∧ x ∈ S ∧ y ∉ S ∧
      Relation.ReflTransGen (fun p q => R p q ∧ p ∈ S ∧ q ∈ S) a x)
    (fun hab ha => ⟨_, _, hab, ha, hb, .refl⟩)
    (fun hab _hcb ih ha => by
      rename_i a' c
      by_cases hc : c ∈ S
      · obtain ⟨x, y, hxy, hxS, hyS, hpref⟩ := ih hc
        exact ⟨x, y, hxy, hxS, hyS, .head ⟨hab, ha, hc⟩ hpref⟩
      · exact ⟨a', c, hab, ha, hc, .refl⟩)

theorem exit_staying_in {α : Type*} {R : α → α → Prop} {S : Set α} {a b : α}
    (h : Relation.ReflTransGen R a b) (ha : a ∈ S) (hb : b ∉ S) :
    ∃ x y, R x y ∧ x ∈ S ∧ y ∉ S ∧
      Relation.ReflTransGen (fun p q => R p q ∧ p ∈ S ∧ q ∈ S) a x := by
  have hne : a ≠ b := fun hab => hb (hab ▸ ha)
  exact exit_helper hb
    ((Relation.reflTransGen_iff_eq_or_transGen.mp h).resolve_left (Ne.symm hne)) ha

/-! ## Connected components in subgraphs -/

variable {W : Type*} [Fintype W] [PseudoMetricSpace W]

omit [Fintype W] in
omit [Fintype V] in
/-- The G-connected component of x within T: all y ∈ T reachable from x via G-edges in T. -/
def graphCompIn (G : SimpleGraph W) (T : Set W) (x : W) : Set W :=
  {y ∈ T | Relation.ReflTransGen (fun a b => a ∈ T ∧ b ∈ T ∧ G.Adj a b) x y}

omit [Fintype W] [PseudoMetricSpace W] in
lemma graphCompIn_subset (G : SimpleGraph W) (T : Set W) (x : W) :
    graphCompIn G T x ⊆ T :=
  fun _ hy => hy.1

omit [Fintype W] [PseudoMetricSpace W] in
lemma graphCompIn_mem (G : SimpleGraph W) (T : Set W) (x : W) (hx : x ∈ T) :
    x ∈ graphCompIn G T x :=
  ⟨hx, Relation.ReflTransGen.refl⟩

omit [Fintype W] [PseudoMetricSpace W] in
lemma graphCompIn_connected (G : SimpleGraph W) (T : Set W) (x : W) (hx : x ∈ T) :
    graphSetConnected G (graphCompIn G T x) := by
  refine' ⟨ ⟨ x, hx, _ ⟩, _ ⟩;
  · rfl;
  · intro y hy z hz
    have h_path : Relation.ReflTransGen (fun a b => a ∈ T ∧ b ∈ T ∧ G.Adj a b) y z := by
      have hyx : Relation.ReflTransGen (fun a b => a ∈ T ∧ b ∈ T ∧ G.Adj a b) y x := by
        have hyx : Relation.ReflTransGen (fun a b => a ∈ T ∧ b ∈ T ∧ G.Adj a b) x y := by
          exact hy.2;
        have hyx : ∀ {a b : W}, Relation.ReflTransGen (fun a b => a ∈ T ∧ b ∈ T ∧ G.Adj a b) a b → Relation.ReflTransGen (fun a b
 => a ∈ T ∧ b ∈ T ∧ G.Adj a b) b a := by
          intro a b hab
          induction' hab with a b hab ih
          generalize_proofs at *; (
          grind +locals);
          exact .single ⟨ ih.2.1, ih.1, ih.2.2.symm ⟩ |> Relation.ReflTransGen.trans <| by assumption;
        generalize_proofs at *; (
        exact hyx ‹_›)
      have hzx : Relation.ReflTransGen (fun a b => a ∈ T ∧ b ∈ T ∧ G.Adj a b) x z := by
        exact hz.2;
      exact hyx.trans hzx
    generalize_proofs at *; (
    have h_path_in_comp : ∀ {a b : W}, Relation.ReflTransGen (fun a b => a ∈ T ∧ b ∈ T ∧ G.Adj a b) a b → a ∈ graphCompIn G T x →
 b ∈ graphCompIn G T x := by
      intro a b hab ha; induction hab <;> simp_all +decide [ graphCompIn ] ; (
      exact Relation.ReflTransGen.tail ‹_› ( by tauto ))
    generalize_proofs at *; (
    have h_path_in_comp : ∀ {a b : W}, Relation.ReflTransGen (fun a b => a ∈ T ∧ b ∈ T ∧ G.Adj a b) a b → a ∈ graphCompIn G T x →
 Relation.ReflTransGen (fun a b => a ∈ graphCompIn G T x ∧ b ∈ graphCompIn G T x ∧ G.Adj a b) a b := by
      intro a b hab ha
      induction' hab with a b hab ih
      generalize_proofs at *; (
      grind +extAll);
      grind
    generalize_proofs at *; (
    exact h_path_in_comp h_path hy)))

omit [Fintype W] [PseudoMetricSpace W] in
lemma graphCompIn_adj_mem {G : SimpleGraph W} {T : Set W} {x y z : W}
    (hy : y ∈ graphCompIn G T x) (hz : z ∈ T) (hadj : G.Adj y z) :
    z ∈ graphCompIn G T x := by
  obtain ⟨hyT, hchain⟩ := hy;
  exact ⟨ hz, hchain.tail ⟨ hyT, hz, hadj ⟩ ⟩

/-! ## Key graph-theory helper: clean connecting path -/

omit [PseudoMetricSpace W] in
theorem clean_connecting_path {G : SimpleGraph W} {S A B : Set W}
    (hconn : graphSetConnected G S)
    (hA : (A ∩ S).Nonempty) (hB : (B ∩ S).Nonempty)
    (hAB_disj : Disjoint (A ∩ S) (B ∩ S))
    (hno_adj : ∀ x ∈ A ∩ S, ∀ y ∈ B ∩ S, ¬G.Adj x y) :
    ∃ P ⊆ S \ (A ∪ B),
      P.Nonempty ∧
      graphSetConnected G P ∧
      (∃ a ∈ A ∩ S, ∃ p ∈ P, G.Adj a p) ∧
      (∃ b ∈ B ∩ S, ∃ q ∈ P, G.Adj b q) := by
  revert hA hB hAB_disj hno_adj hconn;
  intro hS hA hB hAB hno_adj
  by_contra! h_contra;
  have h_no_edge : ∀ z ∈ S \ (A ∪ B), ∀ b ∈ B ∩ S,
      ¬(∃ p ∈ graphCompIn G (S \ (A ∪ B)) z, G.Adj p b) ∨
      ∀ a ∈ A ∩ S, ¬(∃ p ∈ graphCompIn G (S \ (A ∪ B)) z, G.Adj p a) := by
    intro z hz b hb
    by_cases h_edge : ∃ p ∈ graphCompIn G (S \ (A ∪ B)) z, G.Adj p b;
    · refine' Or.inr fun a ha ⟨ p, hp, hap ⟩ => _;
      specialize h_contra ( graphCompIn G ( S \ ( A ∪ B ) ) z ) ?_ ?_ ?_ ?_ b hb;
      · exact fun x hx => hx.1;
      · exact ⟨ p, hp ⟩;
      · exact graphCompIn_connected G ( S \ ( A ∪ B ) ) z hz;
      · exact ⟨ a, ha, p, hp, hap.symm ⟩;
      · exact h_contra _ h_edge.choose_spec.1 ( h_edge.choose_spec.2.symm );
    · exact Or.inl h_edge;
  set X := A ∩ S ∪ {z ∈ S \ (A ∪ B) | ∀ b ∈ B ∩ S, ¬(∃ p ∈ graphCompIn G (S \ (A ∪ B)) z, G.Adj p b)}
  set Y := B ∩ S ∪ {z ∈ S \ (A ∪ B) | ∃ b ∈ B ∩ S, ∃ p ∈ graphCompIn G (S \ (A ∪ B)) z, G.Adj p b};
  have h_no_edge_XY : ∀ x ∈ X, ∀ y ∈ Y, ¬G.Adj x y := by
    rintro x ( hx | hx ) y ( hy | hy );
    · exact hno_adj x hx y hy;
    · obtain ⟨ hy₁, b, hb₁, p, hp₁, hp₂ ⟩ := hy;
      specialize h_no_edge y hy₁ b hb₁;
      cases h_no_edge <;> simp_all +decide [ SimpleGraph.adj_comm ];
      rename_i huggestions;
      exact fun h => huggestions x hx.1 hx.2 y ( by
        exact ⟨ ⟨ hy₁.1, by aesop ⟩, by rfl ⟩ ) h;
    · exact fun h => hx.2 y hy ⟨ x, graphCompIn_mem G ( S \ ( A ∪ B ) ) x hx.1, h ⟩;
    · intro hxy;
      obtain ⟨ b, hb, p, hp, hpb ⟩ := hy.2;
      have h_chain : Relation.ReflTransGen (fun a b => a ∈ S \ (A ∪ B) ∧ b ∈ S \ (A ∪ B) ∧ G.Adj a b) x y := by
        exact .single ⟨ hx.1, hy.1, hxy ⟩;
      have h_chain : p ∈ graphCompIn G (S \ (A ∪ B)) x := by
        exact ⟨ hp.1, h_chain.trans hp.2 ⟩;
      exact hx.2 b hb ⟨ p, h_chain, hpb ⟩;
  have hX_nonempty : X.Nonempty := by
    exact hA.mono fun x hx => Or.inl hx
  have hY_nonempty : Y.Nonempty := by
    exact hB.mono fun x hx => Or.inl hx;
  have hX_Y_disjoint : Disjoint X Y := by
    simp +zetaDelta at *;
    simp +contextual [ Set.disjoint_left ];
    exact fun x hx₁ hx₂ hx₃ => hAB.le_bot ⟨ ⟨ hx₁, hx₂ ⟩, ⟨ hx₃, hx₂ ⟩ ⟩;
  have hX_Y_union : X ∪ Y = S := by
    ext z; by_cases hz : z ∈ A ∪ B <;> simp +decide ;
    · grind;
    · grind;
  obtain ⟨ x, hx ⟩ := hX_nonempty
  obtain ⟨ y, hy ⟩ := hY_nonempty
  have h_chain : Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ G.Adj a b) x y := by
    exact hS.2 x ( hX_Y_union ▸ Set.mem_union_left _ hx ) y ( hX_Y_union ▸ Set.mem_union_right _ hy );
  have := exit_staying_in h_chain hx ( show y ∉ X from fun h => hX_Y_disjoint.le_bot ⟨ h, hy ⟩ );
  grind

/-! ## Disjointness from distance -/

omit [Fintype W] in
theorem no_adj_of_far {G : SimpleGraph W} {δ : ℝ}
    (hedge : ∀ x y : W, G.Adj x y → dist x y ≤ δ)
    {A B : Set W} (hfar : ∀ a ∈ A, ∀ b ∈ B, δ < dist a b) :
    ∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b := by
  exact fun a ha b hb hab => not_lt_of_ge ( hedge a b hab ) ( hfar a ha b hb )

omit [Fintype W] in
theorem disjoint_of_far {δ : ℝ}
    {A B : Set W} (hfar : ∀ a ∈ A, ∀ b ∈ B, δ < dist a b) (hδ : 0 ≤ δ) :
    Disjoint A B := by
  exact Set.disjoint_left.mpr fun x hx h'x => not_lt_of_ge hδ ( hfar x hx x h'x |> lt_of_lt_of_le <| by simp +decide )

/-! ## Helper lemmas about δ-components -/

omit [Fintype V] in
theorem different_components_dist {δ : ℝ} {X : Set V} {x y : V}
    (hx : x ∈ X) (hy : y ∈ X)
    (hcomp : ¬Relation.ReflTransGen (chainRel X δ) x y) :
    δ < dist x y := by
  by_contra h; push_neg at h
  exact hcomp (Relation.ReflTransGen.single ⟨hx, hy, h⟩)

omit [Fintype V] in
theorem deltaComponent_deltaConnected {δ : ℝ} {X : Set V} {x : V} (hx : x ∈ X) :
    deltaConnected δ (deltaComponent δ X x) := by
  refine' ⟨ ⟨ x, hx, _ ⟩, fun y hy z hz => _ ⟩;
  · rfl;
  · have hyz : Relation.ReflTransGen (chainRel X δ) y z := by
      have h_path : Relation.ReflTransGen (chainRel X δ) x y ∧ Relation.ReflTransGen (chainRel X δ) x z := by
        exact ⟨ hy.2, hz.2 ⟩;
      have h_path_symm : ∀ {a b : V}, Relation.ReflTransGen (chainRel X δ) a b → Relation.ReflTransGen (chainRel X δ) b a := by
        intro a b hab;
        induction hab;
        · grind;
        · rename_i h₁ h₂ h₃;
          exact h₃.head ( by exact ⟨ h₂.2.1, h₂.1, by simpa only [ dist_comm ] using h₂.2.2 ⟩ );
      exact h_path_symm h_path.1 |> Relation.ReflTransGen.trans <| h_path.2;
    have hyz_lift : ∀ {u v : V}, u ∈ deltaComponent δ X x → v ∈ deltaComponent δ X x → Relation.ReflTransGen (chainRel X δ) u v →
 Relation.ReflTransGen (chainRel (deltaComponent δ X x) δ) u v := by
      intros u v hu hv huv;
      induction huv;
      · exact .refl;
      · rename_i b c hb hc ih;
        have hb : b ∈ deltaComponent δ X x := by
          exact ⟨ hc.1, hu.2.trans hb ⟩;
        exact ih hb |> fun h => h.tail ( by exact ⟨ hb, hv, hc.2.2 ⟩ );
    exact hyz_lift hy hz hyz

omit [Fintype V] in
theorem connected_growth_point {δ : ℝ} {K X : Set V}
    (hK : deltaConnected δ K) (hX : deltaConnected δ X) (hXK : X ⊆ K) (hne : X ≠ K) :
    ∃ p ∈ K \ X, deltaConnected δ (X ∪ {p}) := by
  obtain ⟨a, ha⟩ : ∃ a ∈ X, ∃ b ∈ K \ X, Relation.ReflTransGen (chainRel K δ) a b := by
    obtain ⟨a, ha⟩ : ∃ a ∈ X, True := by
      exact ⟨ hX.1.choose, hX.1.choose_spec, trivial ⟩
    obtain ⟨b, hb⟩ : ∃ b ∈ K \ X, True := by
      exact Set.exists_of_ssubset ( lt_of_le_of_ne hXK hne ) |> fun ⟨ b, hb₁, hb₂ ⟩ => ⟨ b, ⟨ hb₁, hb₂ ⟩, trivial ⟩
    have h_chain : Relation.ReflTransGen (chainRel K δ) a b := by
      exact hK.2 a ( hXK ha.1 ) b hb.1.1
    use a, ha.left, b, hb.left;
  obtain ⟨ b, hb, h ⟩ := ha.2;
  induction' h with c hc ih ih;
  · grind;
  · cases' em ( c ∈ X ) with hcX hcX <;> simp_all +decide [ chainRel ];
    refine' ⟨ hc, ⟨ ih.2.1, hb ⟩, _, _ ⟩;
    · exact ⟨ hc, Set.mem_insert _ _ ⟩;
    · intro x hx y hy;
      rcases hx with ( rfl | hx ) <;> rcases hy with ( rfl | hy );
      · exact .refl;
      · have := hX.2 c hcX y hy;
        have h_chain : Relation.ReflTransGen (chainRel (insert x X) δ) x c := by
          apply_rules [ Relation.ReflTransGen.single ];
          exact ⟨ Set.mem_insert _ _, Set.mem_insert_of_mem _ hcX, by simpa only [ dist_comm ] using ih.2.2 ⟩;
        exact h_chain.trans ( this.mono fun a b hab => by exact ⟨ Set.mem_insert_of_mem _ hab.1, Set.mem_insert_of_mem _ hab.2.1,
 hab.2.2 ⟩ );
      · have := hX.2 x hx c hcX;
        refine' this.mono _ |> Relation.ReflTransGen.tail <| _;
        · exact fun a b hab => ⟨ Set.mem_insert_of_mem _ hab.1, Set.mem_insert_of_mem _ hab.2.1, hab.2.2 ⟩;
        · exact ⟨ by aesop, by aesop, ih.2.2 ⟩;
      · have := hX.2 x hx y hy;
        exact this.mono fun u v huv => ⟨ Set.mem_insert_of_mem _ huv.1, Set.mem_insert_of_mem _ huv.2.1, huv.2.2 ⟩

omit [Fintype V] in
theorem setBall_Y_Z_dist {ρ δ : ℝ} {X Y C : Set V}
    (_hρ : 0 ≤ ρ) (_hδ : 0 ≤ δ) (_hXC : X ⊆ C) (_hYC : Y ⊆ C)
    (hY_comp : ∀ y ∈ Y, ∀ z ∈ C, Relation.ReflTransGen (chainRel C δ) y z → z ∈ Y)
    (_hXY : ∀ x ∈ X, ∀ y ∈ Y, ¬Relation.ReflTransGen (chainRel C δ) x y) :
    ∀ a ∈ setBall X ρ ∪ Y, ∀ z ∈ C \ (setBall X (ρ + δ) ∪ Y), δ < dist a z := by
  rintro a (⟨x, hx, hal⟩ | hy) z ⟨hz₁, hz₂⟩
  · contrapose! hz₂; exact Or.inl ⟨x, hx, by linarith [dist_triangle x a z]⟩
  · contrapose! hz₂
    exact Or.inr (hY_comp a hy z hz₁ (Relation.ReflTransGen.single ⟨_hYC hy, hz₁, hz₂⟩))

/-! ## Component closure lemmas -/

omit [Fintype V] in
theorem deltaComponent_closed {δ : ℝ} {C : Set V} {c₀ : V} (_hc₀ : c₀ ∈ C) :
    ∀ y ∈ deltaComponent δ C c₀, ∀ z ∈ C,
      Relation.ReflTransGen (chainRel C δ) y z → z ∈ deltaComponent δ C c₀ := by
  exact fun y hy z hz h => ⟨ hz, hy.2.trans h ⟩

omit [Fintype V] in
theorem deltaComponent_disjoint_compClosed {δ : ℝ} {C Y₀ : Set V} {c₀ : V}
    (hc₀ : c₀ ∈ C) (hc₀Y : c₀ ∉ Y₀)
    (hY₀_comp : ∀ y ∈ Y₀, ∀ z ∈ C, Relation.ReflTransGen (chainRel C δ) y z → z ∈ Y₀) :
    Disjoint (deltaComponent δ C c₀) Y₀ := by
  refine' Set.disjoint_left.mpr _;
  intro y hy hy₀;
  have h_chain : Relation.ReflTransGen (chainRel C δ) y c₀ := by
    have h_chain_symm : ∀ {a b : V}, Relation.ReflTransGen (chainRel C δ) a b → Relation.ReflTransGen (chainRel C δ) b a := by
      intro a b hab;
      induction hab;
      · rfl;
      · rename_i h₁ h₂ h₃;
        exact h₃.head ( by exact ⟨ h₂.2.1, h₂.1, by simpa only [ dist_comm ] using h₂.2.2 ⟩ );
    exact h_chain_symm hy.2;
  exact hc₀Y ( hY₀_comp y hy₀ c₀ hc₀ h_chain )

omit [Fintype V] in
theorem union_component_compClosed {δ : ℝ} {C K Y₀ : Set V} {c₀ : V}
    (_hc₀ : c₀ ∈ C) (hK : K = deltaComponent δ C c₀)
    (_hY₀_sub : Y₀ ⊆ C)
    (hY₀_comp : ∀ y ∈ Y₀, ∀ z ∈ C, Relation.ReflTransGen (chainRel C δ) y z → z ∈ Y₀) :
    ∀ y ∈ K ∪ Y₀, ∀ z ∈ C, Relation.ReflTransGen (chainRel C δ) y z → z ∈ K ∪ Y₀ := by
  intro y hy z hz h;
  cases hy <;> simp_all +decide [ deltaComponent ];
  · exact Or.inl ( Relation.ReflTransGen.trans ( by tauto ) h );
  · exact Or.inr ( hY₀_comp _ ‹_› _ hz h )

omit [Fintype V] in
theorem no_chain_component_to_compClosed {δ : ℝ} {C K Y₀ : Set V} {c₀ : V}
    (hc₀ : c₀ ∈ C) (hK : K = deltaComponent δ C c₀)
    (hDisj : Disjoint K Y₀)
    (_hK_sub : K ⊆ C) (hY₀_sub : Y₀ ⊆ C)
    (_hY₀_comp : ∀ y ∈ Y₀, ∀ z ∈ C, Relation.ReflTransGen (chainRel C δ) y z → z ∈ Y₀) :
    ∀ x ∈ K, ∀ y ∈ Y₀, ¬Relation.ReflTransGen (chainRel C δ) x y := by
  intro x hx y hy hxy
  have hyK : y ∈ K := by
    exact hK ▸ deltaComponent_closed hc₀ x ( hK ▸ hx ) y ( hY₀_sub hy ) ( hxy );
  exact Set.disjoint_left.mp hDisj hyK hy

/-! ## Inner growth -/

theorem inner_growth
    (μ : FinOuterMeasure V) (K Y₀ : Set V) (ε η ρ δ : ℝ)
    (_hε : 0 ≤ ε) (_hη : 0 ≤ η) (_hρ : 0 ≤ ρ) (_hδ : 0 ≤ δ)
    (hK : deltaConnected δ K) (hY₀ : μ Y₀ ≤ ε)
    (h_ball : ∀ x : V, μ (setBall {x} ρ) ≤ η) :
    (∃ X ⊆ K, deltaConnected δ X ∧ ε < μ (setBall X ρ ∪ Y₀) ∧
      μ (setBall X ρ ∪ Y₀) ≤ ε + η) ∨
    μ (setBall K ρ ∪ Y₀) ≤ ε := by
  by_contra h_contra;
  obtain ⟨X, hX_sub, hX_max⟩ : ∃ X ⊆ K, deltaConnected δ X ∧ μ.toFun (setBall X ρ ∪ Y₀) ≤ ε ∧ ∀ Y ⊆ K, deltaConnected δ Y → X ⊆ Y
 → μ.toFun (setBall Y ρ ∪ Y₀) ≤ ε → X = Y := by
    have h_well_ordering : ∃ X ∈ {X : Set V | X ⊆ K ∧ deltaConnected δ X ∧ μ.toFun (setBall X ρ ∪ Y₀) ≤ ε}, ∀ Y ∈ {X : Set V | X
⊆ K ∧ deltaConnected δ X ∧ μ.toFun (setBall X ρ ∪ Y₀) ≤ ε}, X.ncard ≥ Y.ncard := by
      apply_rules [ Set.exists_max_image ];
      · exact Set.toFinite _;
      · rcases hK.1 with ⟨ x, hx ⟩;
        refine' ⟨ { x }, _, _, _ ⟩ <;> simp_all +decide;
        · constructor <;> simp +decide;
          rfl;
        · have := h_contra.1 { x } ( by aesop ) ( by
            constructor <;> simp +decide;
            exact Relation.ReflTransGen.refl);
          exact le_of_not_gt fun h => by linarith [ this h, h_ball x, μ.union_le ( setBall { x } ρ ) Y₀ ] ;
    obtain ⟨ X, hX₁, hX₂ ⟩ := h_well_ordering;
    refine' ⟨ X, hX₁.1, hX₁.2.1, hX₁.2.2, fun Y hY₁ hY₂ hY₃ hY₄ => _ ⟩;
    exact Set.eq_of_subset_of_ncard_le hY₃ ( hX₂ Y ⟨ hY₁, hY₂, hY₄ ⟩ );
  obtain ⟨p, hpK, hpX, hp_connected⟩ : ∃ p ∈ K \ X, deltaConnected δ (X ∪ {p}) := by
    apply connected_growth_point hK hX_max.left hX_sub;
    grind;
  have h_outer_measure : μ.toFun (setBall (X ∪ {p}) ρ ∪ Y₀) ≤ μ.toFun (setBall X ρ ∪ Y₀) + μ.toFun (setBall {p} ρ) := by
    have h_outer_measure : μ.toFun (setBall (X ∪ {p}) ρ ∪ Y₀) ≤ μ.toFun ((setBall X ρ ∪ Y₀) ∪ setBall {p} ρ) := by
      refine' μ.mono _;
      simp +decide [ setBall, Set.subset_def ];
      grind;
    exact h_outer_measure.trans ( μ.union_le _ _ );
  refine' h_contra ( Or.inl ⟨ X ∪ { p }, _, _, _, _ ⟩ );
  · exact Set.union_subset hX_sub ( Set.singleton_subset_iff.mpr hpK.1 );
  · exact ⟨ hpX, hp_connected ⟩;
  · exact not_le.mp fun h => hpK.2 <| hX_max.2.2 ( X ∪ { p } ) ( by aesop_cat ) ⟨ hpX, hp_connected ⟩ ( by aesop_cat ) h ▸ by aesop_cat;
  · exact le_trans h_outer_measure ( add_le_add hX_max.2.1 ( h_ball p ) )

/-! ## The greedy growth lemma -/

theorem greedy_growth_aux
    (μ : FinOuterMeasure V) (C Y₀ : Set V)
    (ε η ρ δ : ℝ) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ)
    (hY₀ : μ Y₀ ≤ ε) (hCY₀ : ε < μ (C ∪ Y₀))
    (h_ball : ∀ x : V, μ (setBall {x} ρ) ≤ η) :
    ∃ (X Y : Set V), X ⊆ C ∧ Y ⊆ C ∧ deltaConnected δ X ∧
      ε < μ (setBall X ρ ∪ Y ∪ Y₀) ∧ μ (setBall X ρ ∪ Y ∪ Y₀) ≤ ε + η := by
  revert hCY₀;
  intro hCY₀
  induction' n : Set.ncard C using Nat.strong_induction_on with n ih generalizing C Y₀;
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ ∈ C := by
    contrapose! hCY₀;
    rw [ show C = ∅ by ext; simp +decide [ hCY₀ ] ] ; simpa using hY₀;
  set K := deltaComponent δ C c₀ with hK_def
  have hK_subset : K ⊆ C := by
    exact fun x hx => hx.1
  have hK_deltaConnected : deltaConnected δ K := by
    exact deltaComponent_deltaConnected hc₀;
  have h_inner_growth : (∃ X ⊆ K, deltaConnected δ X ∧ ε < μ (setBall X ρ ∪ Y₀) ∧ μ (setBall X ρ ∪ Y₀) ≤ ε + η) ∨ μ (setBall K ρ ∪ Y₀) ≤ ε := by
    apply inner_growth μ K Y₀ ε η ρ δ hε hη hρ hδ hK_deltaConnected hY₀ h_ball;
  rcases h_inner_growth with ( ⟨ X, hX₁, hX₂, hX₃, hX₄ ⟩ | h_inner_growth );
  · exact ⟨ X, ∅, hX₁.trans hK_subset, Set.empty_subset _, hX₂, by simpa using hX₃, by simpa using hX₄ ⟩;
  · have hK_Y₀ : μ (K ∪ Y₀) ≤ ε := by
      refine' le_trans _ h_inner_growth;
      exact μ.mono ( Set.union_subset_union ( self_subset_setBall _ hρ ) le_rfl );
    set C' := C \ K with hC'_def
    set Y₀' := K ∪ Y₀ with hY₀'_def
    have hC'_ncard : Set.ncard C' < Set.ncard C := by
      rw [ Set.ncard_diff _ _ ];
      · nontriviality;
        exact Nat.sub_lt ( by rw [ Set.ncard_eq_toFinset_card _ ] ; exact Finset.card_pos.mpr ⟨ c₀, by aesop ⟩ ) ( by rw [ Set.ncard_eq_toFinset_card _ ] ; exact Finset.card_pos.mpr ⟨ c₀, by aesop ⟩ );
      · exact hK_subset;
      · exact Set.toFinite K;
    obtain ⟨X, Y', hX₁, hX₂, hX₃, hX₄⟩ : ∃ X Y' : Set V, X ⊆ C' ∧ Y' ⊆ C' ∧ deltaConnected δ X ∧ ε < μ (setBall X ρ ∪ Y' ∪ Y₀') ∧ μ (setBall X ρ ∪ Y' ∪ Y₀') ≤ ε + η := by
      apply ih (Set.ncard C') (by
      exact n ▸ hC'_ncard) C' Y₀' hK_Y₀ (by
      convert hCY₀ using 1;
      congr 1 ; ext x ; by_cases hx : x ∈ K <;> aesop) rfl;
    refine' ⟨ X, Y' ∪ K, _, _, hX₃, _, _ ⟩ <;> simp_all +decide [ Set.union_assoc ];
    · exact fun x hx => hX₁ hx |>.1;
    · exact fun x hx => hX₂ hx |>.1

theorem greedy_growth_gen
    (μ : FinOuterMeasure V) (C Y₀ : Set V)
    (ε η ρ δ : ℝ) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ)
    (hY₀_meas : μ Y₀ ≤ ε) (hC_meas : ε < μ C)
    (hY₀_sub : Y₀ ⊆ C)
    (hY₀_comp : ∀ y ∈ Y₀, ∀ z ∈ C, Relation.ReflTransGen (chainRel C δ) y z → z ∈ Y₀)
    (h_ball : ∀ x : V, μ (setBall {x} ρ) ≤ η) :
    ∃ (X Y : Set V),
      X ⊆ C ∧ Y ⊆ C ∧ deltaConnected δ X ∧
      Y₀ ⊆ Y ∧
      (∀ y ∈ Y, ∀ z ∈ C, Relation.ReflTransGen (chainRel C δ) y z → z ∈ Y) ∧
      (∀ x ∈ X, ∀ y ∈ Y, ¬Relation.ReflTransGen (chainRel C δ) x y) ∧
      ε < μ (setBall X ρ ∪ Y) ∧ μ (setBall X ρ ∪ Y) ≤ ε + η := by
  induction' n : Set.ncard ( C \ Y₀ ) using Nat.strong_induction_on with n ih generalizing Y₀ C;
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ ∈ C ∧ c₀ ∉ Y₀ := by
    exact Set.exists_of_ssubset ( lt_of_le_of_ne hY₀_sub ( by rintro rfl; linarith ) );
  set K := deltaComponent δ C c₀ with hK_def
  have hK_sub : K ⊆ C := by
    exact fun x hx => hx.1
  have hK_deltaConnected : deltaConnected δ K := by
    exact deltaComponent_deltaConnected hc₀.1;
  by_cases h_case : ε < μ (setBall K ρ ∪ Y₀);
  · have := inner_growth μ K Y₀ ε η ρ δ hε hη hρ hδ hK_deltaConnected hY₀_meas h_ball;
    rcases this with ( ⟨ X, hX₁, hX₂, hX₃, hX₄ ⟩ | hX₃ );
    · refine' ⟨ X, Y₀, hX₁.trans hK_sub, hY₀_sub, hX₂, Set.Subset.refl _, hY₀_comp, _, hX₃, hX₄ ⟩;
      intro x hx y hy hxy;
      have := no_chain_component_to_compClosed hc₀.1 rfl ( deltaComponent_disjoint_compClosed hc₀.1 hc₀.2 hY₀_comp ) hK_sub hY₀_sub hY₀_comp x ( hX₁ hx ) y hy hxy; contradiction;
    · linarith;
  · set Y₀' := K ∪ Y₀ with hY₀'_def;
    have hY₀'_sub : Y₀' ⊆ C := by
      exact Set.union_subset hK_sub hY₀_sub
    have hY₀'_sup : Y₀ ⊆ Y₀' := by
      exact Set.subset_union_right
    have hY₀'_comp : ∀ y ∈ Y₀', ∀ z ∈ C, Relation.ReflTransGen (chainRel C δ) y z → z ∈ Y₀' := by
      apply union_component_compClosed hc₀.1 rfl hY₀_sub hY₀_comp
    have hY₀'_card : Set.ncard (C \ Y₀') < Set.ncard (C \ Y₀) := by
      apply_rules [ Set.ncard_lt_ncard ];
      · simp +decide [ Set.ssubset_def, Set.subset_def ];
        exact ⟨ fun x hx hx' => ⟨ hx, fun hx'' => hx' <| Or.inr hx'' ⟩, c₀, hc₀.1, hc₀.2, fun _ => Or.inl <| by exact ⟨ hc₀.1, by
 exact Relation.ReflTransGen.refl ⟩ ⟩;
      · exact Set.toFinite _;
    obtain ⟨X, Y, hX_sub, hY_sub, hX_deltaConnected, hY₀'_sup, hY_comp, hY₀'_card⟩ := ih (Set.ncard (C \ Y₀')) (by
    exact hY₀'_card.trans_le n.le) C Y₀' (by
    refine' le_trans _ ( le_of_not_gt h_case );
    apply_rules [ μ.mono ];
    exact Set.union_subset_union ( self_subset_setBall _ hρ ) Set.Subset.rfl) (by
    exact hC_meas) hY₀'_sub hY₀'_comp rfl;
    exact ⟨ X, Y, hX_sub, hY_sub, hX_deltaConnected, by tauto ⟩

/-- Main greedy growth lemma. -/
theorem greedy_growth
    (μ : FinOuterMeasure V) (C : Set V)
    (ε η ρ δ : ℝ) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ)
    (hC : μ C > ε) (h_ball : ∀ x : V, μ (setBall {x} ρ) ≤ η) :
    ∃ (X Y : Set V),
      X ⊆ C ∧ Y ⊆ C ∧ deltaConnected δ X ∧
      (∀ y ∈ Y, ∀ z ∈ C, Relation.ReflTransGen (chainRel C δ) y z → z ∈ Y) ∧
      (∀ x ∈ X, ∀ y ∈ Y, ¬Relation.ReflTransGen (chainRel C δ) x y) ∧
      ε < μ (setBall X ρ ∪ Y) ∧ μ (setBall X ρ ∪ Y) ≤ ε + η := by
  obtain ⟨X, Y, h1, h2, h3, _, h5, h6, h7, h8⟩ :=
    greedy_growth_gen μ C ∅ ε η ρ δ hε hη hρ hδ
      (by rw [μ.empty]; exact hε) hC (empty_subset _) (by simp) h_ball
  exact ⟨X, Y, h1, h2, h3, h5, h6, h7, h8⟩

/-! ## The main lemma (Lemma 4.1) -/

/-- **Lemma 4.1** (Pure pairs in pseudometric spaces). -/
theorem pure_pairs_lemma
    (n : ℕ) (ε η : ℝ) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hεη : 2 * (n : ℝ) * ε + (n : ℝ) * η < 1)
    (μ : FinOuterMeasure V) (hμ : μ Set.univ = 1)
    (ρ δ : ℝ) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) :
    (∃ x : V, μ (setBall {x} ρ) > η) ∨
    (∃ A B : Set V, μ A > ε ∧ μ B > ε ∧ ∀ a ∈ A, ∀ b ∈ B, δ < dist a b) ∨
    (∃ (f : Fin n → Set V),
      (∀ i, deltaConnected δ (f i)) ∧
      (∀ i j, i ≠ j → ∀ a ∈ f i, ∀ b ∈ f j, ρ < dist a b) ∧
      μ ((⋂ i, setBall (f i) (ρ + δ)) \ setBall (⋃ i, f i) ρ) ≥
        1 - 2 * (n : ℝ) * ε - (n : ℝ) * η) := by
  by_contra hεη;
  push_neg at hεη;
  have h_ind : ∀ k ≤ n, ∃ f : Fin k → Set V,
    (∀ i, deltaConnected δ (f i)) ∧
    (∀ i j, i ≠ j → ∀ a ∈ f i, ∀ b ∈ f j, ρ < dist a b) ∧
    μ.toFun ((⋂ i, setBall (f i) (ρ + δ)) \ setBall (⋃ i, f i) ρ) ≥ 1 - 2 * k * ε - k * η := by
      intro k hk
      induction' k with k ih;
      · simp +decide;
        grind +suggestions;
      · obtain ⟨ f, hf₁, hf₂, hf₃ ⟩ := ih ( Nat.le_of_succ_le hk );
        set C := (⋂ i, setBall (f i) (ρ + δ)) \ setBall (⋃ i, f i) ρ;
        obtain ⟨X, Y, hX_sub, hY_sub, hX_conn, hY_comp, hXY_disj, hXY_lo, hXY_hi⟩ : ∃ X Y : Set V,
          X ⊆ C ∧ Y ⊆ C ∧ deltaConnected δ X ∧
          (∀ y ∈ Y, ∀ z ∈ C, Relation.ReflTransGen (chainRel C δ) y z → z ∈ Y) ∧
          (∀ x ∈ X, ∀ y ∈ Y, ¬Relation.ReflTransGen (chainRel C δ) x y) ∧
          ε < μ.toFun (setBall X ρ ∪ Y) ∧ μ.toFun (setBall X ρ ∪ Y) ≤ ε + η := by
            apply greedy_growth;
            any_goals tauto;
            nlinarith [ show ( k : ℝ ) + 1 ≤ n by norm_cast, show ( k : ℝ ) ≥ 0 by positivity ];
        refine' ⟨ Fin.snoc f X, _, _, _ ⟩;
        · intro i;
          refine' Fin.lastCases _ _ i <;> simp +decide [ * ];
        · intro i j hij a ha b hb;
          by_cases hi : i.val < k <;> by_cases hj : j.val < k <;> simp +decide [ Fin.snoc, * ] at ha hb ⊢;
          · exact hf₂ _ _ ( by simpa [ Fin.ext_iff ] using hij ) _ ha _ hb;
          · exact dist_old_new_gt ( show X ⊆ C from hX_sub ) ( show C ⊆ ( ⋂ i, setBall ( f i ) ( ρ + δ ) ) \ setBall ( ⋃ i, f i ) ρ from Set.Subset.refl _ ) hρ hδ ( i.castLT hi ) a ha b hb;
          · contrapose! hXY_disj;
            have := hX_sub ha;
            exact False.elim ( this.2 ( by exact ⟨ b, Set.mem_iUnion_of_mem _ hb, by simpa [ dist_comm ] using hXY_disj ⟩ ) );
          · exact False.elim ( hij ( Fin.ext ( by linarith [ Fin.is_lt i, Fin.is_lt j ] ) ) );
        · have h_measure_diff : μ.toFun ((C ∩ setBall X (ρ + δ)) \ setBall X ρ) ≥ μ.toFun C - μ.toFun (setBall X ρ ∪ Y) - μ.toFun (C \ (setBall X (ρ + δ) ∪ Y)) := by
            apply measure_bound_step;
          have h_measure_diff_further : μ.toFun (C \ (setBall X (ρ + δ) ∪ Y)) ≤ ε := by
            have h_measure_diff_further : ∀ a ∈ setBall X ρ ∪ Y, ∀ z ∈ C \ (setBall X (ρ + δ) ∪ Y), δ < dist a z := by
              apply setBall_Y_Z_dist hρ hδ (by
              exact hX_sub) (by
              exact hY_sub) hY_comp (by
              exact hXY_disj);
            grind +splitIndPred;
          refine' le_trans _ ( h_measure_diff.trans _ );
          · norm_num; linarith;
          · refine' μ.mono _;
            simp +decide [ Fin.snoc, Set.subset_def ];
            intro x hx₁ hx₂ hx₃;
            refine' ⟨ _, _ ⟩;
            · intro i; cases i using Fin.lastCases <;> simp +decide [ * ] ;
              exact Set.mem_iInter.mp hx₁.1 _;
            · convert hx₁.2 using 1;
              simp +decide [ setBall, Set.mem_iUnion ];
              constructor <;> rintro ⟨ y, ⟨ i, hi ⟩, hy ⟩;
              · split_ifs at hi <;> [ exact ⟨ y, ⟨ _, hi ⟩, hy ⟩ ; exact False.elim ( hx₃ ⟨ y, hi, hy ⟩ ) ];
              · exact ⟨ y, ⟨ ⟨ i, by linarith [ Fin.is_lt i ] ⟩, by simpa [ Fin.castLT ] using hi ⟩, hy ⟩;
  exact absurd ( h_ind n le_rfl ) ( by rintro ⟨ f, hf₁, hf₂, hf₃ ⟩ ; linarith [ hεη.2.2 f hf₁ hf₂ ] )

/-! ## Theorem 4.2: Fat models from pseudometric spaces -/

/-- **Theorem 4.2** (Fat models from pseudometric spaces). -/
theorem pure_pairs_fat_model
    (G : SimpleGraph W) (n m : ℕ) (hm : 1 ≤ m)
    (ε η : ℝ) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    /- Note: The paper states ≤ 1 but the proof requires strict < 1 to apply Lemma 4.1
       and the greedy far-point selection. We use < 1 here. -/
    (hεη : 2 * (n : ℝ) * ε + ((n : ℝ) + (m : ℝ) - 1) * η < 1)
    (μ : FinOuterMeasure W) (hμ : μ Set.univ = 1)
    (H : SimpleGraph (Fin n)) (hm_edges : H.edgeSet.ncard = m)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hG_ball : ∀ (A : Set W),
      deltaConnected δ A → graphSetConnected G (setBall A (δ / 2)))
    (hG_path : ∀ (x : W) (A : Set W) (r : ℝ), A.Nonempty →
      r ≤ 5 * δ →
      (∃ a ∈ A, dist x a ≤ r) →
      ∃ (P : Set W) (a : W), a ∈ A ∩ P ∧ x ∈ P ∧
        graphSetConnected G P ∧ P ⊆ setBall {x} r ∧
        ∀ u ∈ P, dist x u + dist u a = dist x a) :
    (∃ x : W, μ (setBall {x} (11 * δ)) > η) ∨
    (∃ A B : Set W, μ A > ε ∧ μ B > ε ∧ ∀ a ∈ A, ∀ b ∈ B, δ < dist a b) ∨
    Nonempty (FatModel H G δ) := by
  by_cases h1 : ∃ x : W, μ (setBall {x} (11 * δ)) > η
  · exact Or.inl h1
  push_neg at h1
  by_cases h2 : ∃ A B : Set W, μ A > ε ∧ μ B > ε ∧ ∀ a ∈ A, ∀ b ∈ B, δ < dist a b
  · exact Or.inr (Or.inl h2)
  push_neg at h2
  have h_ball : ∀ x : W, μ (setBall {x} (4 * δ)) ≤ η :=
    fun x => le_trans (μ.mono (setBall_mono_radius _ (by linarith))) (h1 x)
  have hεη_n : 2 * (n : ℝ) * ε + (n : ℝ) * η < 1 := by
    nlinarith [show (m : ℝ) ≥ 1 from by exact_mod_cast hm]
  rcases pure_pairs_lemma n ε η hε hη hεη_n μ hμ (4 * δ) δ (by linarith) hδ with
    ⟨x, hx⟩ | ⟨A, B, hA, hB, hAB⟩ | ⟨f, hf_conn, hf_dist, hf_meas⟩
  · exact absurd (h1 x) (not_le.mpr (lt_of_lt_of_le hx (μ.mono (setBall_mono_radius _ (by linarith)))))
  · exact Or.inr (Or.inl ⟨A, B, hA, hB, hAB⟩)
  · set C := (⋂ i, setBall (f i) (4 * δ + δ)) \ setBall (⋃ i, f i) (4 * δ) with hC_def
    obtain ⟨pts, hpts_mem, hpts_dist⟩ := greedy_far_points μ C (11 * δ) η hη
      (fun x => h1 x) m (by nlinarith)
    have hpts_near : ∀ k i, ∃ a ∈ f i, dist (pts k) a ≤ 5 * δ := by
      intro k i
      have := ((hpts_mem k).1 : pts k ∈ ⋂ i, setBall (f i) (4 * δ + δ))
      obtain ⟨a, ha, hd⟩ := Set.mem_iInter.mp this i
      exact ⟨a, ha, by rw [dist_comm]; linarith⟩
    have hpts_far_f : ∀ k i a, a ∈ f i → 4 * δ < dist a (pts k) := by
      intro k i a ha
      by_contra hle; push_neg at hle
      exact (hpts_mem k).2 ⟨a, Set.mem_iUnion.mpr ⟨i, ha⟩, hle⟩
    have henum_card : Fintype.card H.edgeSet = m := by
      rwa [← Set.toFinset_card, ← Set.ncard_eq_toFinset_card']
    let enum : H.edgeSet ≃ Fin m := Fintype.equivFinOfCardEq henum_card
    let ePt : H.edgeSet → W := fun e => pts (enum e)
    let eFst : H.edgeSet → Fin n := fun e => (Quot.out e.val).1
    let eSnd : H.edgeSet → Fin n := fun e => (Quot.out e.val).2
    have eEndpoints : ∀ e : H.edgeSet, e.val = s(eFst e, eSnd e) :=
      fun e => (Quot.out_eq e.val).symm
    have path_fst : ∀ e : H.edgeSet,
        ∃ (P : Set W) (a : W), a ∈ f (eFst e) ∩ P ∧ ePt e ∈ P ∧
          graphSetConnected G P ∧ P ⊆ setBall {ePt e} (5 * δ) ∧
          ∀ u ∈ P, dist (ePt e) u + dist u a = dist (ePt e) a :=
      fun e => hG_path _ _ _ (hf_conn (eFst e)).1 le_rfl (hpts_near (enum e) (eFst e))
    have path_snd : ∀ e : H.edgeSet,
        ∃ (P : Set W) (a : W), a ∈ f (eSnd e) ∩ P ∧ ePt e ∈ P ∧
          graphSetConnected G P ∧ P ⊆ setBall {ePt e} (5 * δ) ∧
          ∀ u ∈ P, dist (ePt e) u + dist u a = dist (ePt e) a :=
      fun e => hG_path _ _ _ (hf_conn (eSnd e)).1 le_rfl (hpts_near (enum e) (eSnd e))
    let Pfst : H.edgeSet → Set W := fun e => (path_fst e).choose
    let afst : H.edgeSet → W := fun e => (path_fst e).choose_spec.choose
    let Psnd : H.edgeSet → Set W := fun e => (path_snd e).choose
    let asnd : H.edgeSet → W := fun e => (path_snd e).choose_spec.choose
    have hPf : ∀ e, afst e ∈ f (eFst e) ∩ Pfst e ∧ ePt e ∈ Pfst e ∧
        graphSetConnected G (Pfst e) ∧ Pfst e ⊆ setBall {ePt e} (5 * δ) ∧
        ∀ u ∈ Pfst e, dist (ePt e) u + dist u (afst e) = dist (ePt e) (afst e) :=
      fun e => (path_fst e).choose_spec.choose_spec
    have hPs : ∀ e, asnd e ∈ f (eSnd e) ∩ Psnd e ∧ ePt e ∈ Psnd e ∧
        graphSetConnected G (Psnd e) ∧ Psnd e ⊆ setBall {ePt e} (5 * δ) ∧
        ∀ u ∈ Psnd e, dist (ePt e) u + dist u (asnd e) = dist (ePt e) (asnd e) :=
      fun e => (path_snd e).choose_spec.choose_spec
    have hE_sub : ∀ e, Pfst e ∪ Psnd e ⊆ setBall {ePt e} (5 * δ) :=
      fun e => Set.union_subset (hPf e).2.2.2.1 (hPs e).2.2.2.1
    have eMem : ∀ (e : H.edgeSet) (v : Fin n), v ∈ e.val ↔ v = eFst e ∨ v = eSnd e := by
      intro e v; rw [eEndpoints e, Sym2.mem_iff]
    refine Or.inr (Or.inr ⟨{
      vertexMap := fun i => setBall (f i) (δ / 2)
      edgeMap := fun e => Pfst e ∪ Psnd e
      vertex_connected := fun i => hG_ball _ (hf_conn i)
      edge_connected := by
        intro e;
        obtain ⟨ P, hP ⟩ := hPf e |>.2.2.1;
        obtain ⟨ Q, hQ ⟩ := hPs e |>.2.2.1;
        refine' ⟨ _, _ ⟩;
        · exact ⟨ _, Set.mem_union_left _ ( hPf e |>.2.1 ) ⟩;
        · intro x hx y hy;
          rcases hx with ( hx | hx ) <;> rcases hy with ( hy | hy );
          · exact hP x hx y hy |> fun h => h.mono fun a b hab => ⟨ Or.inl hab.1, Or.inl hab.2.1, hab.2.2 ⟩;
          · have h_path : Relation.ReflTransGen (fun a b => a ∈ Pfst e ∪ Psnd e ∧ b ∈ Pfst e ∪ Psnd e ∧ G.Adj a b) x (ePt e) :=
 by
              have := hP x hx ( ePt e ) ( hPf e |>.2.1 );
              exact this.mono fun a b hab => ⟨ Or.inl hab.1, Or.inl hab.2.1, hab.2.2 ⟩;
            have h_path : Relation.ReflTransGen (fun a b => a ∈ Pfst e ∪ Psnd e ∧ b ∈ Pfst e ∪ Psnd e ∧ G.Adj a b) (ePt e) y :=
 by
              have := hQ ( ePt e ) ( hPs e |>.2.1 ) y hy;
              exact this.mono fun a b hab => ⟨ Or.inr hab.1, Or.inr hab.2.1, hab.2.2 ⟩;
            exact Relation.ReflTransGen.trans ‹_› ‹_›;
          · have h_path : Relation.ReflTransGen (fun a b => a ∈ Psnd e ∧ b ∈ Psnd e ∧ G.Adj a b) x (ePt e) ∧ Relation.ReflTransGen (fun a b => a ∈ Pfst e ∧ b ∈ Pfst e ∧ G.Adj a b) (ePt e) y := by
              exact ⟨ hQ x hx ( ePt e ) ( hPs e |>.2.1 ), hP ( ePt e ) ( hPf e |>.2.1 ) y hy ⟩;
            exact h_path.1.mono ( by rintro a b ⟨ ha, hb, hab ⟩ ; exact ⟨ Or.inr ha, Or.inr hb, hab ⟩ ) |> Relation.ReflTransGen.trans <| h_path.2.mono ( by rintro a b ⟨ ha, hb, hab ⟩ ; exact ⟨ Or.inl ha, Or.inl hb, hab ⟩ );
          · exact hQ x hx y hy |> fun h => h.mono fun a b hab => ⟨ Or.inr hab.1, Or.inr hab.2.1, hab.2.2 ⟩
      incident_intersect := by
        intro v e hv
        rw [eMem e v] at hv
        rcases hv with (hv | hv);
        · refine' ⟨ afst e, _, _ ⟩;
          · rw [ hv ];
            exact ⟨ afst e, hPf e |>.1.1, by norm_num; linarith ⟩;
          · exact Or.inl ( hPf e |>.1 |>.2 );
        · use asnd e;
          simp +decide [ hv, setBall ];
          grind +qlia
      vertex_vertex_far := by
        intros v w hvw a ha b hb
        obtain ⟨av, hav, hdav⟩ := ha
        obtain ⟨bw, hbw, hdbw⟩ := hb
        have h_dist : dist a b ≥ dist av bw - dist av a - dist b bw := by
          linarith [ dist_triangle4_right av bw a b, dist_comm b bw ];
        linarith [ hf_dist v w hvw av hav bw hbw, dist_comm b bw ]
      edge_edge_far := by
        intros e f hne a ha b hb;
        have h_dist : dist (ePt e) a ≤ 5 * δ ∧ dist (ePt f) b ≤ 5 * δ := by
          have := hE_sub e ha; have := hE_sub f hb; simp +decide [ setBall ] at *;
          exact ⟨ by assumption, by assumption ⟩;
        have h_dist : dist (ePt e) (ePt f) > 11 * δ := by
          exact hpts_dist _ _ ( by simpa [ enum.injective.eq_iff ] using hne );
        linarith [ dist_triangle4_right ( ePt e ) ( ePt f ) a b, dist_comm ( ePt f ) b ]
      nonincident_far := by
        intro v e hv a ha b hb
        by_contra h_contra
        have hdav : ∃ av ∈ f v, dist av a ≤ δ / 2 := by
          exact ⟨ _, ha.choose_spec.1, by simpa only [ dist_comm ] using ha.choose_spec.2 ⟩;
        by_cases hb_fst : b ∈ Pfst e;
        · obtain ⟨av, hav⟩ := hdav
          have h_dist_av_b : dist av b ≤ 3 * δ / 2 := by
            linarith [ dist_triangle av a b ]
          have h_dist_av_ePt : 4 * δ < dist av (ePt e) := by
            exact hpts_far_f ( enum e ) v av hav.1
          have h_dist_av_afst : 4 * δ < dist av (afst e) := by
            grind
          have h_dist_ePt_b : 5 * δ / 2 < dist (ePt e) b := by
            linarith [ dist_triangle_left av ( ePt e ) b, dist_triangle_left av ( ePt e ) ( afst e ), dist_triangle_left av b ( afst e ), dist_comm av b, dist_comm av ( ePt e ), dist_comm av ( afst e ), dist_comm b ( ePt e ), dist_comm b ( afst e ), dist_comm ( ePt e ) ( afst e ) ]
          have h_dist_b_afst : dist b (afst e) ≤ 5 * δ / 2 := by
            have := hPf e |>.2.2.2.2 b hb_fst;
            linarith [ show dist ( ePt e ) ( afst e ) ≤ 5 * δ by exact le_of_not_gt fun h => by have := hPf e |>.2.2.2.1 ( hPf e |>.1.2 ) ; exact absurd this ( by simp +decide [ setBall ] ; linarith ) ]
          have h_dist_av_afst_le : dist av (afst e) ≤ 4 * δ := by
            linarith [dist_triangle av b (afst e)]
          linarith [h_dist_av_b, h_dist_av_ePt, h_dist_av_afst, h_dist_ePt_b, h_dist_b_afst, h_dist_av_afst_le];
        · obtain ⟨av, hav⟩ := hdav
          have h_dist_av_b : dist av b ≤ 3 * δ / 2 := by
            linarith [ dist_triangle av a b ]
          have h_dist_av_pt : dist av (ePt e) > 4 * δ := by
            exact hpts_far_f _ _ _ hav.1
          have h_dist_pt_b : dist (ePt e) b > 5 * δ / 2 := by
            linarith [ dist_triangle_right av ( ePt e ) b ];
          have h_dist_b_asnd : dist b (asnd e) ≤ 5 * δ / 2 := by
            have := hPs e |>.2.2.2.1 ( hPs e |>.1.2 );
            obtain ⟨ x, hx, hx' ⟩ := this;
            grind
          have h_dist_av_asnd : dist av (asnd e) ≤ 4 * δ := by
            linarith [ dist_triangle av b ( asnd e ) ]
          have h_contra : 4 * δ < dist av (asnd e) ∧ dist av (asnd e) ≤ 4 * δ := by
            exact ⟨ hf_dist v ( eSnd e ) ( by rintro rfl; exact hv ( eMem e _ |>.2 ( Or.inr rfl ) ) ) av hav.1 ( asnd e ) ( hPs e
 |>.1.1 ), h_dist_av_asnd ⟩
          linarith [h_contra.left, h_contra.right]
    }⟩)

/-! ## Theorem 4.3: Induced minors of 1-subdivisions -/

private lemma edge_endpoints_ne {V : Type*} {H : SimpleGraph V}
    (e : H.edgeSet) : (Quot.out e.val).1 ≠ (Quot.out e.val).2 := by
  have := e.2;
  rw [ ← Quot.out_eq e.val ] at this;
  grind +suggestions

private lemma edge_inner_set
    {n : ℕ} {H : SimpleGraph (Fin n)} {G : SimpleGraph W} {δ : ℝ}
    (hδ : 0 ≤ δ) (hG_metric : ∀ x y, G.Adj x y → dist x y ≤ δ)
    (F : FatModel H G δ) (e : H.edgeSet) :
    ∃ P ⊆ F.edgeMap e \ (F.vertexMap (Quot.out e.val).1 ∪ F.vertexMap (Quot.out e.val).2),
      P.Nonempty ∧ graphSetConnected G P ∧
      (∃ a ∈ F.vertexMap (Quot.out e.val).1, ∃ p ∈ P, G.Adj a p) ∧
      (∃ b ∈ F.vertexMap (Quot.out e.val).2, ∃ q ∈ P, G.Adj b q) := by
  have := @CoarsePurePairs.clean_connecting_path;
  specialize @this W _ G ( F.edgeMap e ) ( F.vertexMap ( Quot.out e.val ).1 ) ( F.vertexMap ( Quot.out e.val ).2 ) ( F.edge_connected e ) ?_ ?_ ?_ ?_;
  · exact F.incident_intersect _ _ ( Sym2.out_fst_mem _ );
  · convert F.incident_intersect _ _ ( Sym2.out_snd_mem e.val ) using 1;
  · refine' Set.disjoint_left.mpr _;
    intro a ha hb
    have h_dist : δ < dist a a := by
      have := F.vertex_vertex_far ( Quot.out e.val ).1 ( Quot.out e.val ).2 ( edge_endpoints_ne e ) a ha.1 a hb.1; aesop;
    norm_num at h_dist ; linarith;
  · intro x hx y hy hxy;
    have := F.vertex_vertex_far ( Quot.out e.val ).1 ( Quot.out e.val ).2 ( edge_endpoints_ne e ) x hx.1 y hy.1;
    linarith [ hG_metric x y hxy ];
  · exact ⟨ this.choose, this.choose_spec.1, this.choose_spec.2.1, this.choose_spec.2.2.1, by obtain ⟨ a, ha, p, hp, hap ⟩ := this.choose_spec.2.2.2.1; exact ⟨ a, ha.1, p, hp, hap ⟩, by obtain ⟨ b, hb, q, hq, hbq ⟩ := this.choose_spec.2.2.2.2; exact ⟨ b, hb.1, q, hq, hbq ⟩ ⟩

omit [Fintype W] in
private lemma fatModel_pairwise_disjoint
    {n : ℕ} {H : SimpleGraph (Fin n)} {G : SimpleGraph W} {δ : ℝ}
    (hδ : 0 ≤ δ) (_hG_metric : ∀ x y, G.Adj x y → dist x y ≤ δ)
    (F : FatModel H G δ)
    (P : H.edgeSet → Set W)
    (hP_sub : ∀ e, P e ⊆ F.edgeMap e \ (F.vertexMap (Quot.out e.val).1 ∪ F.vertexMap (Quot.out e.val).2)) :
    let map_fn : Fin n ⊕ H.edgeSet → Set W
      | Sum.inl v => F.vertexMap v
      | Sum.inr e => P e
    Pairwise (Disjoint on map_fn) := by
  intro x y hxy;
  rcases y with ( y | y ) <;> rcases hxy with ( hxy | hxy ) <;> simp_all +decide;
  · exact fun h => disjoint_of_far ( fun a ha b hb => F.vertex_vertex_far _ _ h _ ha _ hb ) hδ;
  · by_cases hy : y ∈ hxy.val;
    · have := Quot.out_eq hxy.val;
      grind +qlia;
    · have := F.nonincident_far y hxy hy;
      exact Set.disjoint_left.mpr fun a ha₁ ha₂ => by linarith [ this a ha₁ a ( hP_sub _ hxy.2 ha₂ |>.1 ), dist_self a ] ;
  · by_cases h : hxy ∈ y.val <;> simp_all +decide [ Set.disjoint_left ];
    · have := Quot.out_eq y.val;
      grind;
    · intro a ha hb; have := F.nonincident_far hxy y h; simp_all +decide [ Set.subset_def ] ;
      exact not_le_of_gt ( this _ hb _ ( hP_sub _ y.2 _ ha |>.1 ) ) ( dist_self a ▸ hδ );
  · intro hy
    have h_edge_map : ∀ a ∈ F.edgeMap y, ∀ b ∈ F.edgeMap hxy, δ < dist a b := by
      exact F.edge_edge_far y hxy hy;
    exact Set.disjoint_left.mpr fun a ha₁ ha₂ => by have := h_edge_map a ( hP_sub _ y.2 ha₁ |>.1 ) a ( hP_sub _ hxy.2 ha₂ |>.1 ); linarith [ @dist_self W _ a ] ;

omit [Fintype W] in
private lemma fatModel_adj_edge
    {n : ℕ} {H : SimpleGraph (Fin n)} {G : SimpleGraph W} {δ : ℝ}
    (_hδ : 0 ≤ δ) (_hG_metric : ∀ x y, G.Adj x y → dist x y ≤ δ)
    (F : FatModel H G δ)
    (P : H.edgeSet → Set W)
    (_hP_sub : ∀ e, P e ⊆ F.edgeMap e \ (F.vertexMap (Quot.out e.val).1 ∪ F.vertexMap (Quot.out e.val).2))
    (hP_adj_fst : ∀ e, ∃ a ∈ F.vertexMap (Quot.out e.val).1, ∃ p ∈ P e, G.Adj a p)
    (hP_adj_snd : ∀ e, ∃ b ∈ F.vertexMap (Quot.out e.val).2, ∃ q ∈ P e, G.Adj b q) :
    let map_fn : Fin n ⊕ H.edgeSet → Set W
      | Sum.inl v => F.vertexMap v
      | Sum.inr e => P e
    ∀ u v, (graphOneSubdiv H).Adj u v → ∃ a ∈ map_fn u, ∃ b ∈ map_fn v, G.Adj a b := by
  simp +decide [ graphOneSubdiv ];
  constructor;
  · intro v e he hv;
    have h_cases : v = (Quot.out e).1 ∨ v = (Quot.out e).2 := by
      have := Quot.out_eq e;
      grind +splitImp;
    rcases h_cases with ( rfl | rfl ) <;> [ exact hP_adj_fst ⟨ e, he ⟩ ; exact hP_adj_snd ⟨ e, he ⟩ ];
  · intro e he x hx;
    obtain hx_fst | hx_snd : x = (Quot.out e).1 ∨ x = (Quot.out e).2 := by
      have := Quot.out_eq e;
      grind +splitIndPred;
    · obtain ⟨ a, ha, p, hp, hap ⟩ := hP_adj_fst ⟨ e, he ⟩ ; use p, hp, a, by simpa [ hx_fst ] using ha; ; exact hap.symm;
    · obtain ⟨ b, hb, q, hq, h ⟩ := hP_adj_snd ⟨ e, he ⟩ ; use q, hq, b, by aesop; ; exact h.symm;

omit [Fintype W] in
private lemma fatModel_nonadj_noedge
    {n : ℕ} {H : SimpleGraph (Fin n)} {G : SimpleGraph W} {δ : ℝ}
    (_hδ : 0 ≤ δ) (hG_metric : ∀ x y, G.Adj x y → dist x y ≤ δ)
    (F : FatModel H G δ)
    (P : H.edgeSet → Set W)
    (hP_sub : ∀ e, P e ⊆ F.edgeMap e \ (F.vertexMap (Quot.out e.val).1 ∪ F.vertexMap (Quot.out e.val).2)) :
    let map_fn : Fin n ⊕ H.edgeSet → Set W
      | Sum.inl v => F.vertexMap v
      | Sum.inr e => P e
    ∀ u v, u ≠ v → ¬(graphOneSubdiv H).Adj u v → ∀ a ∈ map_fn u, ∀ b ∈ map_fn v, ¬G.Adj a b := by
  intro map_fn u v huv huv' a ha b hb hab; rcases u with ( u | u ) <;> rcases v with ( v | v ) <;> simp_all +decide [ graphOneSubdiv ] ;
  · exact absurd ( hG_metric a b hab ) ( by linarith [ F.vertex_vertex_far u v huv a ha b hb ] );
  · exact absurd ( hG_metric a b hab ) ( by linarith [ F.nonincident_far u v huv' a ha b ( hP_sub _ v.2 hb |>.1 ) ] );
  · have := F.nonincident_far v u huv';
    exact not_le_of_gt ( this b hb a ( hP_sub _ _ ha |>.1 ) ) ( by simpa only [ dist_comm ] using hG_metric _ _ hab );
  · have := F.edge_edge_far ⟨ _, u.2 ⟩ ⟨ _, v.2 ⟩ ( by aesop ) a ( hP_sub _ u.2 ha |>.1 ) b ( hP_sub _ v.2 hb |>.1 ) ; linarith [
 hG_metric _ _ hab ] ;

/-- Convert a FatModel to an internal induced minor model of the 1-subdivision. -/
theorem fatModel_to_hasInducedMinor_internal
    {n : ℕ} {H : SimpleGraph (Fin n)} {G : SimpleGraph W} {δ : ℝ}
    (hδ : 0 ≤ δ) (hG_metric : ∀ x y, G.Adj x y → dist x y ≤ δ)
    (F : FatModel H G δ) :
    HasInducedMinor_internal G (graphOneSubdiv H) := by
  have hP := fun e => edge_inner_set hδ hG_metric F e
  choose P hP_sub hP_ne hP_conn hP_adj_fst hP_adj_snd using hP
  let map_fn : Fin n ⊕ H.edgeSet → Set W
    | Sum.inl v => F.vertexMap v
    | Sum.inr e => P e
  exact ⟨{
    branch := map_fn
    branch_connected := by
      intro v; cases v with
      | inl v => exact graphSetConnected_to_induce_connected _ _ (F.vertex_connected v)
      | inr e => exact graphSetConnected_to_induce_connected _ _ (hP_conn e)
    branch_disjoint := fun w₁ w₂ hne =>
      fatModel_pairwise_disjoint hδ hG_metric F P hP_sub hne
    adj_preserved := fatModel_adj_edge hδ hG_metric F P hP_sub hP_adj_fst hP_adj_snd
    nonadj_preserved := fatModel_nonadj_noedge hδ hG_metric F P hP_sub
  } ⟩

/-- **Theorem 4.3** (Induced minors of 1-subdivisions). -/
theorem pure_pairs_subdiv
    (G : SimpleGraph W) (n m : ℕ) (hm : 1 ≤ m)
    (ε η : ℝ) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hεη : (2 * (n : ℝ) + 2) * ε + ((n : ℝ) + (m : ℝ)) * η < 1)
    (w : W → ℝ) (_hw : ∀ x, 0 ≤ w x)
    (_hedge : ∀ x y, G.Adj x y → dist x y ≤ (w x + w y) / 2)
    (μ : FinOuterMeasure W) (hμ : μ Set.univ = 1)
    (H : SimpleGraph (Fin n)) (hm_edges : H.edgeSet.ncard = m)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hG_metric : ∀ x y, G.Adj x y → dist x y ≤ δ)
    (hG_ball : ∀ (A : Set W),
      deltaConnected δ A → graphSetConnected G (setBall A (δ / 2)))
    (hG_path : ∀ (x : W) (A : Set W) (r : ℝ), A.Nonempty →
      r ≤ 5 * δ →
      (∃ a ∈ A, dist x a ≤ r) →
      ∃ (P : Set W) (a : W), a ∈ A ∩ P ∧ x ∈ P ∧
        graphSetConnected G P ∧ P ⊆ setBall {x} r ∧
        ∀ u ∈ P, dist x u + dist u a = dist x a) :
    (∃ x : W, μ (setBall {x} (11 * δ)) > η) ∨
    (∃ A B : Set W, μ A > ε ∧ μ B > ε ∧ ∀ a ∈ A, ∀ b ∈ B, δ < dist a b) ∨
    HasInducedMinor_internal G (graphOneSubdiv H) := by
  have hεη' : 2 * (n : ℝ) * ε + ((n : ℝ) + (m : ℝ) - 1) * η < 1 := by nlinarith
  have h_result := pure_pairs_fat_model G n m hm ε η hε hη hεη' μ hμ H hm_edges δ hδ
    hG_ball hG_path
  rcases h_result with h_ball | h_pair | h_model
  · exact Or.inl h_ball
  · exact Or.inr (Or.inl h_pair)
  · obtain ⟨F⟩ := h_model
    exact Or.inr (Or.inr (fatModel_to_hasInducedMinor_internal hδ hG_metric F))

end CoarsePurePairs
