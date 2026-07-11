import Mathlib
import InducedMinorFreeSeparators.ConcurrentFlowProof.Defs
import InducedMinorFreeSeparators.ConcurrentFlowProof.CombLLL
import InducedMinorFreeSeparators.ConcurrentFlowProof.ProductIndep
import InducedMinorFreeSeparators.ConcurrentFlowProof.LLLProof
import InducedMinorFreeSeparators.ConcurrentFlowProof.GraphHelpers

open Finset SimpleGraph Real MeasureTheory Classical
open scoped BigOperators NNReal ENNReal

noncomputable section

namespace PathTableLLL

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  {W : Type*} [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {H : SimpleGraph W} [DecidableRel H.Adj]

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-! ### Product Space -/

abbrev DP (V : Type*) [DecidableEq V] := {p : V × V // p.1 ≠ p.2}
abbrev Idx := W ⊕ (H.edgeFinset × DP V)

def VPF (cf : ConcurrentFlow G) (a b : V) : Finset (List V) :=
  cf.support.filter (fun l => l.head? = some a ∧ l.getLast? = some b)

def Beta (cf : ConcurrentFlow G) : Idx (W := W) (H := H) (V := V) → Type _
  | Sum.inl _ => V
  | Sum.inr ⟨_, ⟨⟨a, b⟩, _⟩⟩ => ↥(VPF cf a b)

instance instFT (cf : ConcurrentFlow G) (i : Idx (W := W) (H := H) (V := V)) :
    Fintype (Beta cf i) := by
  unfold Beta; split <;> exact inferInstance

def Wt (cf : ConcurrentFlow G) :
    ∀ (i : Idx (W := W) (H := H) (V := V)), Beta cf i → ℝ≥0∞
  | Sum.inl _, _ => (Fintype.card V : ℝ≥0∞)⁻¹
  | Sum.inr _, l => (cf.flow l.val : ℝ≥0∞)

lemma wt_sum_one (cf : ConcurrentFlow G) :
    ∀ i : Idx (W := W) (H := H) (V := V), ∑ b : Beta cf i, Wt cf i b = 1 := by
  intro i; cases i with
  | inl w =>
    show ∑ _ : V, (Fintype.card V : ℝ≥0∞)⁻¹ = 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.mul_inv_cancel]
    · exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    · exact ENNReal.natCast_ne_top _
  | inr p =>
    obtain ⟨e, ⟨⟨a, b⟩, hab⟩⟩ := p
    convert cf.total_flow a b hab using 1;
    convert ( ENNReal.coe_inj );
    any_goals exact ∑ l ∈ cf.support.filter ( fun l => l.head? = some a ∧ l.getLast? = some b ), cf.flow l;
    · simp +decide [ Wt, VPF ];
      refine' Finset.sum_bij ( fun x _ => x.val ) _ _ _ _ <;> simp +decide;
      exact fun l hl hl' hl'' => ⟨ ⟨ l, Finset.mem_filter.mpr ⟨ hl, hl', hl'' ⟩ ⟩, rfl ⟩;
    · norm_cast

def getV (cf : ConcurrentFlow G) (f : ∀ i : Idx (W := W) (H := H) (V := V), Beta cf i)
    (w : W) : V :=
  f (Sum.inl w)

/-! ### Canonical ordering for edge pairs -/

/-- A canonical well-ordering on H.edgeFinset, used to break symmetry in MIP events.
    We use a well-ordering relation to define a linear order. -/
noncomputable instance edgeFinsetLinearOrder :
    LinearOrder (↥(H.edgeFinset)) :=
  IsWellOrder.linearOrder WellOrderingRel

/-- Canonical ordering predicate for edge pairs. -/
def edgeLT (e₁ e₂ : ↥(H.edgeFinset)) : Prop :=
  @LT.lt _ edgeFinsetLinearOrder.toLT e₁ e₂

noncomputable instance edgeLT_decidable (e₁ e₂ : ↥(H.edgeFinset)) : Decidable (edgeLT e₁ e₂) :=
  Classical.dec _

/-! ### Bad Events -/

abbrev BIdx := H.edgeFinset ⊕ (H.edgeFinset × H.edgeFinset)

def collEv (cf : ConcurrentFlow G) (e : H.edgeFinset) :
    Set (∀ i : Idx (W := W) (H := H) (V := V), Beta cf i) :=
  {f | getV cf f e.val.out.1 = getV cf f e.val.out.2}

def mipEv (cf : ConcurrentFlow G) (e₁ e₂ : H.edgeFinset) :
    Set (∀ i : Idx (W := W) (H := H) (V := V), Beta cf i) :=
  if e₁ = e₂ then ∅
  else if e₁.val.out.1 = e₂.val.out.1 then ∅
  else if e₁.val.out.1 = e₂.val.out.2 then ∅
  else if e₁.val.out.2 = e₂.val.out.1 then ∅
  else if e₁.val.out.2 = e₂.val.out.2 then ∅
  else {f |
    if h₁ : getV cf f e₁.val.out.1 ≠ getV cf f e₁.val.out.2 then
      if h₂ : getV cf f e₂.val.out.1 ≠ getV cf f e₂.val.out.2 then
        ¬MutuallyInducedPaths G
          (f (Sum.inr ⟨e₁, ⟨(getV cf f e₁.val.out.1, getV cf f e₁.val.out.2), h₁⟩⟩) :
            Beta cf (Sum.inr ⟨e₁, ⟨(getV cf f e₁.val.out.1, getV cf f e₁.val.out.2), h₁⟩⟩)).val
          (f (Sum.inr ⟨e₂, ⟨(getV cf f e₂.val.out.1, getV cf f e₂.val.out.2), h₂⟩⟩) :
            Beta cf (Sum.inr ⟨e₂, ⟨(getV cf f e₂.val.out.1, getV cf f e₂.val.out.2), h₂⟩⟩)).val
      else False
    else False}

/-- The bad events. For MIP events, only canonical pairs (edgeLT e₁ e₂) are active;
    non-canonical pairs are trivially empty. This halves the effective dependency degree. -/
def bEv (cf : ConcurrentFlow G) :
    BIdx (W := W) (H := H) → Set (∀ i : Idx (W := W) (H := H) (V := V), Beta cf i)
  | Sum.inl e => collEv cf e
  | Sum.inr ⟨e₁, e₂⟩ => if edgeLT e₁ e₂ then mipEv cf e₁ e₂ else ∅

instance instDecBEv (cf : ConcurrentFlow G) (k : BIdx (W := W) (H := H))
    (f : ∀ i : Idx (W := W) (H := H) (V := V), Beta cf i) :
    Decidable (f ∈ bEv cf k) := by
  unfold bEv; cases k with
  | inl e => unfold collEv; simp only [Set.mem_setOf_eq]; infer_instance
  | inr p =>
    obtain ⟨e₁, e₂⟩ := p
    by_cases h : edgeLT e₁ e₂
    · simp only [h, if_pos]; unfold mipEv
      repeat split_ifs
      all_goals first
        | exact instDecidableFalse
        | (simp only [Set.mem_setOf_eq]; infer_instance)
    · simp only [h, if_neg, not_false_eq_true]; exact instDecidableFalse

/-! ### Dependency Structure -/

/-- Dependency set: the set of product-space coordinates that the event depends on.
    For non-canonical MIP pairs, this is ∅ since the event is empty. -/
def bDep : BIdx (W := W) (H := H) → Finset (Idx (W := W) (H := H) (V := V))
  | Sum.inl e => {Sum.inl e.val.out.1, Sum.inl e.val.out.2}
  | Sum.inr ⟨e₁, e₂⟩ =>
    if edgeLT e₁ e₂ then
      ({Sum.inl e₁.val.out.1, Sum.inl e₁.val.out.2,
        Sum.inl e₂.val.out.1, Sum.inl e₂.val.out.2} : Finset _) ∪
      (Finset.univ.image (fun p : DP V => (Sum.inr ⟨e₁, p⟩ : Idx))) ∪
      (Finset.univ.image (fun p : DP V => (Sum.inr ⟨e₂, p⟩ : Idx)))
    else ∅

lemma bDep_spec (cf : ConcurrentFlow G) (k : BIdx (W := W) (H := H)) :
    ∀ f₁ f₂ : ∀ i : Idx (W := W) (H := H) (V := V), Beta cf i,
      (∀ i ∈ bDep k, f₁ i = f₂ i) →
      (f₁ ∈ bEv cf k ↔ f₂ ∈ bEv cf k) := by
  intro f₁ f₂ h
  cases k with
  | inl e =>
    simp only [bEv, collEv, Set.mem_setOf_eq, getV]
    have h1 := h (Sum.inl e.val.out.1) (by simp [bDep])
    have h2 := h (Sum.inl e.val.out.2) (by simp [bDep])
    rw [h1, h2]
  | inr p =>
    obtain ⟨e₁, e₂⟩ := p
    simp only [bEv]
    by_cases hlt : edgeLT e₁ e₂
    · simp only [hlt, if_pos]
      simp only [bDep, hlt, if_pos] at h
      unfold mipEv; simp +decide [getV] at h ⊢
      grind +suggestions
    · simp only [hlt, if_neg, not_false_eq_true]; exact Iff.rfl

/-- Vertex-endpoint set. Empty for non-canonical MIP events. -/
def bVertices : BIdx (W := W) (H := H) → Finset W
  | Sum.inl e => {e.val.out.1, e.val.out.2}
  | Sum.inr ⟨e₁, e₂⟩ =>
    if edgeLT e₁ e₂ then {e₁.val.out.1, e₁.val.out.2, e₂.val.out.1, e₂.val.out.2}
    else ∅

/-- The dependency graph: two events are neighbors if they share a vertex endpoint. -/
def bGamma : BIdx (W := W) (H := H) → Finset (BIdx (W := W) (H := H)) :=
  fun k => Finset.univ.filter (fun k' =>
    k' ≠ k ∧ ¬Disjoint (bVertices k) (bVertices k'))

lemma bGamma_self :
    ∀ k : BIdx (W := W) (H := H), k ∉ bGamma k := by
  intro k; simp [bGamma]

lemma bDep_disjoint_of_bVertices_disjoint
    (k₁ k₂ : BIdx (W := W) (H := H))
    (hv : Disjoint (bVertices k₁) (bVertices (H := H) k₂)) :
    Disjoint (bDep (V := V) k₁) (bDep (V := V) k₂) := by
  cases' k₁ with e k₁;
  · cases k₂ <;> simp_all +decide [ bVertices, bDep ];
    split_ifs at * <;> simp_all +decide [ Finset.mem_insert, Finset.mem_singleton ];
  · cases' k₂ with e k₂;
    · unfold bDep; simp +decide ;
      split_ifs <;> simp_all +decide [ bVertices ];
    · unfold bDep bVertices at *;
      by_cases h₁ : edgeLT k₁.1 k₁.2 <;> by_cases h₂ : edgeLT k₂.1 k₂.2 <;> simp +decide [ h₁, h₂ ] at hv ⊢;
      simp +decide [ Finset.disjoint_left, hv ];
      grind

lemma bGamma_disjoint :
    ∀ k₁ k₂ : BIdx (W := W) (H := H),
      k₂ ∉ bGamma k₁ → k₂ ≠ k₁ →
      Disjoint (bDep (V := V) k₁) (bDep (V := V) k₂) := by
  intro k₁ k₂ h hne
  simp only [bGamma, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not] at h
  exact bDep_disjoint_of_bVertices_disjoint k₁ k₂ (h hne)

/-! ### Bounds -/

/-
Non-canonical MIP events are empty, so probability = 0.
-/
private lemma prob_bound_noncanonical (cf : ConcurrentFlow G) (e₁ e₂ : H.edgeFinset)
    (hlt : ¬edgeLT e₁ e₂) (hEH : 1 < H.edgeFinset.card) :
    letI : MeasurableSpace (∀ i : Idx (W := W) (H := H) (V := V), Beta cf i) := ⊤
    ((weightedPMF (fun f => ∏ i, Wt cf i (f i))
      (total_weight_ne_zero (Wt cf) (wt_sum_one cf))
      (total_weight_ne_top (Wt cf) (wt_sum_one cf))).toMeasure (bEv cf (Sum.inr ⟨e₁, e₂⟩))).toReal ≤
    1 / (48 * H.edgeFinset.card + 52 : ℝ) := by
      rw [ show bEv cf ( Sum.inr ( e₁, e₂ ) ) = ∅ from ?_ ];
      · simp +decide [ weightedPMF ];
        positivity;
      · exact if_neg hlt

/-
Collision events have probability 1/|V| ≤ 1/(48|E(H)|+52).
-/
private lemma prob_bound_collision (cf : ConcurrentFlow G) (e : H.edgeFinset)
    (_hV : 2 ≤ Fintype.card V) (hEH : 1 < H.edgeFinset.card)
    (h100 : 100 * H.edgeFinset.card < Fintype.card V) :
    letI : MeasurableSpace (∀ i : Idx (W := W) (H := H) (V := V), Beta cf i) := ⊤
    ((weightedPMF (fun f => ∏ i, Wt cf i (f i))
      (total_weight_ne_zero (Wt cf) (wt_sum_one cf))
      (total_weight_ne_top (Wt cf) (wt_sum_one cf))).toMeasure (bEv cf (Sum.inl e))).toReal ≤
    1 / (48 * H.edgeFinset.card + 52 : ℝ) := by
      rw [ prod_measure_eq ];
      · -- The sum of the weights for the collision event is equal to the probability of the collision event, which is 1/|V|.
        have h_sum_weights : (∑ f : ∀ i : Idx (W := W) (H := H) (V := V), Beta cf i, if f (Sum.inl e.val.out.1) = f (Sum.inl e.val.out.2) then ∏ i, Wt cf i (f i) else 0) = (Fintype.card V : ℝ≥0∞)⁻¹ := by
          have := @two_coord_prob;
          convert Finset.sum_congr rfl fun v _ => this ( Wt cf ) ( wt_sum_one cf ) ( Sum.inl ( e.val.out.1 ) ) ( Sum.inl ( e.val.out.2 ) ) _ v v using 1;
          any_goals exact H;
          any_goals exact Finset.univ;
          any_goals try infer_instance;
          · rw [ ← Finset.sum_comm ];
            refine' Finset.sum_congr rfl fun x hx => _;
            rw [ Finset.sum_eq_single ( x ( Sum.inl ( Quot.out e.val ).1 ) ) ] <;> simp +decide;
            · simp +decide only [eq_comm];
            · tauto;
          · unfold Wt; simp +decide ;
            unfold Beta; simp +decide ;
            simp +decide [ ← mul_assoc, ENNReal.mul_inv_cancel, show Fintype.card V ≠ 0 by linarith ];
          · cases e ; simp +decide [ Quot.out ];
            rename_i e he;
            have := Classical.choose_spec ( show ∃ p : W × W, p.1 ≠ p.2 ∧ Sym2.mk p = ‹Sym2 W› from by
                                              rename_i x;
                                              rcases x with ⟨ a, b ⟩;
                                              exact ⟨ ( a, b ), by simpa using SimpleGraph.ne_of_adj H ( by simpa using e ), rfl ⟩ )
            generalize_proofs at *;
            grind;
        -- Convert the sum of the weights to a real number.
        have h_real_sum_weights : (∑ f : ∀ i : Idx (W := W) (H := H) (V := V), Beta cf i, if f (Sum.inl e.val.out.1) = f (Sum.inl e.val.out.2) then ∏ i, Wt cf i (f i) else 0).toReal = 1 / (Fintype.card V : ℝ) := by
          rw [ h_sum_weights, ENNReal.toReal_inv, ENNReal.toReal_natCast ] ; norm_num;
        convert h_real_sum_weights.le.trans _ using 1;
        gcongr ; norm_cast ; linarith;
      · -- By definition of Wt, we know that for each i, the sum of Wt cf i b over all b is 1.
        intros i
        apply wt_sum_one

/-
Squaring the congestion bound: 0 ≤ C ≤ n²/(15√m√e) implies C² ≤ n⁴/(225me).
-/
private lemma congestion_sq_le (n m e : ℕ) (C : ℝ)
    (hC : C ≤ (n : ℝ)^2 / (15 * Real.sqrt m * Real.sqrt e))
    (hC0 : 0 ≤ C) (_hm : 0 < m) (_he : 0 < e) :
    C ^ 2 ≤ (n : ℝ) ^ 4 / (225 * m * e) := by
      convert pow_le_pow_left₀ hC0 hC 2 using 1 ; ring_nf ; norm_num [ _hm.le, _he.le ] ;

/-
Pure natural number arithmetic: (48m+52)(n+2e) ≤ 225me when e ≥ n-1, n > 100m, m ≥ 2.
-/
private lemma mip_nat_arith (n m e : ℕ) (he : n - 1 ≤ e) (hn : 100 * m < n) (hm : 1 < m) :
    (48 * m + 52) * (n + 2 * e) ≤ 225 * m * e := by
      nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ n ) ]

/-
The arithmetic bound: C²(n+2e)/n⁴ ≤ 1/(48m+52) given congestion bound,
    e ≥ n-1, n > 100m, m ≥ 2, n > 1796.
-/
private lemma mip_final_arith
    (n m e : ℕ) (C : ℝ)
    (hC : C ≤ (n : ℝ)^2 / (15 * Real.sqrt m * Real.sqrt e))
    (hC0 : 0 ≤ C)
    (he : n - 1 ≤ e) (hn : 100 * m < n) (hm : 1 < m) (hn2 : 1796 < n)
    (_hV2 : 2 ≤ n) :
    C ^ 2 * ((n : ℝ) + 2 * e) / (n : ℝ) ^ 4 ≤ 1 / (48 * (m : ℝ) + 52) := by
      have hcsq := congestion_sq_le n m e C hC hC0 (by omega) (by omega);
      rw [ div_le_div_iff₀ ] <;> try positivity;
      refine le_trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right hcsq ( by positivity ) ) ( by positivity ) ) ?_;
      rw [ div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ ];
      · have := mip_nat_arith n m e he hn hm;
        norm_cast ; nlinarith only [ this, pow_pos ( by linarith : 0 < n ) 4 ];
      · exact mul_pos ( by positivity ) ( Nat.cast_pos.mpr ( by omega ) )

/-- A concurrent flow on G implies G has at least |V|-1 edges (G must be connected). -/
private lemma cf_edge_count (cf : ConcurrentFlow G) (hV : 2 ≤ Fintype.card V) :
    Fintype.card V - 1 ≤ G.edgeFinset.card :=
  cf.edge_count hV

/-- The congestion of a concurrent flow is non-negative. -/
private lemma congestion_nonneg (cf : ConcurrentFlow G) : 0 ≤ cf.congestion := by
  unfold ConcurrentFlow.congestion ConcurrentFlow.vertexFlow
  apply le_trans _ (Finset.le_sup' _ (Finset.mem_univ (Classical.arbitrary V)))
  positivity

/-- The vertex flow at v is at most the congestion. -/
private lemma vertexFlow_le_congestion (cf : ConcurrentFlow G) (v : V) :
    cf.vertexFlow v ≤ cf.congestion := by
  exact Finset.le_sup' _ (Finset.mem_univ v)

/-- The ENNReal sum over mipEv is at most 1. -/
private lemma mipEv_sum_le_one (cf : ConcurrentFlow G) (e₁ e₂ : H.edgeFinset) :
    (∑ f : ∀ i : Idx (W := W) (H := H) (V := V), Beta cf i,
      if f ∈ mipEv cf e₁ e₂ then ∏ i, Wt cf i (f i) else 0) ≤ 1 := by
  calc ∑ f, (if f ∈ mipEv cf e₁ e₂ then ∏ i, Wt cf i (f i) else 0)
      ≤ ∑ f, ∏ i, Wt cf i (f i) :=
        Finset.sum_le_sum fun f _ => by split_ifs <;> simp
    _ = 1 := total_weight_one (Wt cf) (wt_sum_one cf)

/-- The path for edge e through vertex assignments (a,b) that passes through vertex v
    has total flow at most vertexFlow(v). Specifically,
    ∑_{l ∈ VPF(a,b) : v ∈ l} flow(l) ≤ vertexFlow(v) -/
private lemma path_flow_through_le_vf (cf : ConcurrentFlow G) (v a b : V) :
    (∑ l ∈ (VPF cf a b).filter (fun l => v ∈ l), (cf.flow l : ℝ)) ≤ cf.vertexFlow v := by
  unfold ConcurrentFlow.vertexFlow VPF
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro l hl; simp only [Finset.mem_filter] at hl ⊢; exact ⟨hl.1.1, hl.2⟩
  · intro _ _ _; positivity

/-! ### Helper lemmas for the ENNReal measure bound -/

/-
¬MutuallyInducedPaths implies existence of a "bad" vertex pair:
    either a shared vertex or a G-edge between the two paths.
-/
private lemma not_mip_bad_pair (l₁ l₂ : List V)
    (h : ¬MutuallyInducedPaths G l₁ l₂) :
    ∃ v₁ ∈ l₁, ∃ v₂ ∈ l₂, v₁ = v₂ ∨ G.Adj v₁ v₂ := by
  contrapose! h;
  constructor;
  · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => h x ( List.mem_toFinset.mp hx₁ ) x ( List.mem_toFinset.mp hx₂ ) |>.1 rfl;
  · exact fun v₁ hv₁ v₂ hv₂ => h v₁ hv₁ v₂ hv₂ |>.2

/-
Weighted union bound: if every f ∈ A belongs to some B(k) for k ∈ S,
    then the weighted sum over A is at most the sum over S of weighted sums over B(k).
-/
private lemma ennreal_weighted_union_bound
    {κ : Type*}
    (w : (∀ i : Idx (W := W) (H := H) (V := V), Beta cf i) → ℝ≥0∞)
    (A : Set (∀ i : Idx (W := W) (H := H) (V := V), Beta cf i))
    [∀ f, Decidable (f ∈ A)]
    (B : κ → Set (∀ i : Idx (W := W) (H := H) (V := V), Beta cf i))
    [∀ k, ∀ f, Decidable (f ∈ B k)]
    (S : Finset κ)
    (h : ∀ f ∈ A, ∃ k ∈ S, f ∈ B k) :
    (∑ f, if f ∈ A then w f else 0) ≤
    ∑ k ∈ S, ∑ f, if f ∈ B k then w f else 0 := by
  -- By hypothesis h, for each f in A, there exists a k in S such that f is in B k. Therefore, the sum over f in A of w f is less than or equal to the sum over k in S of the sum over f in B k of w f.
  have h_sum_le : ∀ f ∈ A, ∑ k ∈ S, (if f ∈ B k then w f else 0) ≥ w f := by
    intro f hf; obtain ⟨ k, hk₁, hk₂ ⟩ := h f hf; exact le_trans ( by aesop ) ( Finset.single_le_sum ( fun x _ => by positivity ) hk₁ ) ;
  rw [ ← Finset.sum_comm ];
  exact Finset.sum_le_sum fun f _ => by by_cases hf : f ∈ A <;> simp +decide [ hf, h_sum_le f ] ;

/-- The event "v is on the path for edge e" in the product space. -/
private def onPathEv (cf : ConcurrentFlow G) (e : H.edgeFinset) (v : V) :
    Set (∀ i : Idx (W := W) (H := H) (V := V), Beta cf i) :=
  {f | if h : getV cf f e.val.out.1 ≠ getV cf f e.val.out.2 then
         v ∈ (f (Sum.inr ⟨e, ⟨(getV cf f e.val.out.1, getV cf f e.val.out.2), h⟩⟩) :
           Beta cf _).val
       else False}

private instance instDecOnPathEv (cf : ConcurrentFlow G) (e : H.edgeFinset) (v : V)
    (f : ∀ i : Idx (W := W) (H := H) (V := V), Beta cf i) :
    Decidable (f ∈ onPathEv cf e v) := by
  unfold onPathEv; simp only [Set.mem_setOf_eq]; infer_instance

/-
mipEv is contained in the union of onPathEv intersections over bad vertex pairs.
-/
private lemma mipEv_subset_union (cf : ConcurrentFlow G) (e₁ e₂ : H.edgeFinset)
    (hne : e₁ ≠ e₂)
    (h1 : e₁.val.out.1 ≠ e₂.val.out.1) (h2 : e₁.val.out.1 ≠ e₂.val.out.2)
    (h3 : e₁.val.out.2 ≠ e₂.val.out.1) (h4 : e₁.val.out.2 ≠ e₂.val.out.2) :
    ∀ f, f ∈ mipEv cf e₁ e₂ →
      ∃ p ∈ (Finset.univ : Finset (V × V)).filter (fun p => p.1 = p.2 ∨ G.Adj p.1 p.2),
        f ∈ onPathEv cf e₁ p.1 ∩ onPathEv cf e₂ p.2 := by
  intro f hf;
  unfold mipEv at hf; simp_all +decide ;
  obtain ⟨ h₁, h₂, h₃ ⟩ := hf; have := not_mip_bad_pair _ _ h₃; obtain ⟨ a, ha, b, hb, hab ⟩ := this; use a, b; simp_all +decide [ onPathEv ] ;

/-
The onPathEv event depends only on coordinates for edge e.
-/
private lemma onPathEv_dep (cf : ConcurrentFlow G) (e : H.edgeFinset) (v : V) :
    ∀ f₁ f₂ : ∀ i : Idx (W := W) (H := H) (V := V), Beta cf i,
      (∀ i, (i = Sum.inl e.val.out.1 ∨ i = Sum.inl e.val.out.2 ∨
             ∃ q : DP V, i = Sum.inr ⟨e, q⟩) → f₁ i = f₂ i) →
      (f₁ ∈ onPathEv cf e v ↔ f₂ ∈ onPathEv cf e v) := by
  intro f₁ f₂ h
  simp [onPathEv];
  simp +decide [ getV, h ];
  grind

/-
The dependency sets for non-incident edges are disjoint.
-/
private lemma edge_dep_disjoint (e₁ e₂ : H.edgeFinset)
    (_hne : e₁ ≠ e₂)
    (h1 : e₁.val.out.1 ≠ e₂.val.out.1) (h2 : e₁.val.out.1 ≠ e₂.val.out.2)
    (h3 : e₁.val.out.2 ≠ e₂.val.out.1) (h4 : e₁.val.out.2 ≠ e₂.val.out.2) :
    Disjoint
      (({Sum.inl e₁.val.out.1, Sum.inl e₁.val.out.2} :
          Finset (Idx (W := W) (H := H) (V := V))) ∪
        Finset.univ.image (fun q : DP V => (Sum.inr ⟨e₁, q⟩ : Idx)))
      (({Sum.inl e₂.val.out.1, Sum.inl e₂.val.out.2} :
          Finset (Idx (W := W) (H := H) (V := V))) ∪
        Finset.univ.image (fun q : DP V => (Sum.inr ⟨e₂, q⟩ : Idx))) := by
  simp +decide [ *, Finset.disjoint_left , Finset.mem_image ];
  grind

/-- For the easy case: the weighted sum of any event is ≤ 1. -/
private lemma onPathEv_sum_le_one (cf : ConcurrentFlow G) (e : H.edgeFinset) (v : V) :
    (∑ f, if f ∈ onPathEv cf e v then ∏ i, Wt cf i (f i) else 0) ≤ 1 := by
  calc ∑ f, (if f ∈ onPathEv cf e v then ∏ i, Wt cf i (f i) else 0)
      ≤ ∑ f, ∏ i, Wt cf i (f i) := Finset.sum_le_sum fun f _ => by split_ifs <;> simp
    _ = 1 := total_weight_one (Wt cf) (wt_sum_one cf)

/-- The fixed-endpoint event: f(w₁) = a, f(w₂) = b, v ∈ path(a,b). -/
private def onPathEvFixed (cf : ConcurrentFlow G) (e : H.edgeFinset) (v a b : V) (h : a ≠ b) :
    Set (∀ i : Idx (W := W) (H := H) (V := V), Beta cf i) :=
  {f | f (Sum.inl e.val.out.1) = a ∧ f (Sum.inl e.val.out.2) = b ∧
       v ∈ (f (Sum.inr ⟨e, ⟨(a, b), h⟩⟩) : Beta cf _).val}

private instance instDecOnPathEvFixed (cf : ConcurrentFlow G) (e : H.edgeFinset) (v a b : V)
    (h : a ≠ b) (f : ∀ i : Idx (W := W) (H := H) (V := V), Beta cf i) :
    Decidable (f ∈ onPathEvFixed cf e v a b h) := by
  unfold onPathEvFixed; simp only [Set.mem_setOf_eq]; infer_instance

/-
onPathEv ⊆ union of fixed-endpoint events over all (a,b) with a ≠ b.
-/
private lemma onPathEv_subset_fixed (cf : ConcurrentFlow G) (e : H.edgeFinset) (v : V) :
    ∀ f, f ∈ onPathEv cf e v →
      ∃ (a b : V) (h : a ≠ b), f ∈ onPathEvFixed cf e v a b h := by
  intro f hf;
  unfold onPathEv at hf;
  unfold onPathEvFixed; aesop;

/-
Each fixed-endpoint term equals (1/n)² * flow through v for paths from a to b.
-/
private lemma onPathEvFixed_eq (cf : ConcurrentFlow G) (e : H.edgeFinset) (v a b : V)
    (h : a ≠ b) :
    (∑ f, if f ∈ onPathEvFixed cf e v a b h then ∏ i, Wt cf i (f i) else 0) =
    (Fintype.card V : ℝ≥0∞)⁻¹ * (Fintype.card V : ℝ≥0∞)⁻¹ *
    ∑ l ∈ (VPF cf a b).filter (fun l => v ∈ l),
      (cf.flow l : ℝ≥0∞) := by
  convert three_coord_mixed_prob ( fun i b => Wt cf i b ) ( wt_sum_one cf ) ( Sum.inl e.val.out.1 ) ( Sum.inl e.val.out.2 ) ( Sum.inr ⟨ e, ⟨ ( a, b ), h ⟩ ⟩ ) _ _ _ a b _ using 1;
  any_goals exact Finset.univ.filter fun l => v ∈ l.val;
  · simp +decide [ onPathEvFixed ];
  · unfold Wt; simp +decide [ Finset.sum_filter ] ;
    refine' congr_arg _ ( Finset.sum_bij ( fun x hx => ⟨ x, by aesop ⟩ ) _ _ _ _ ) <;> simp +decide;
    lia;
  · have := Quot.out_eq e.val;
    cases h : Quot.out ( e : Sym2 W ) ; aesop;
  · grind;
  · grind

/-
The weighted sum of onPathEv is bounded by C/n² (as ENNReal).
-/
private lemma onPathEv_weighted_sum_le (cf : ConcurrentFlow G) (e : H.edgeFinset) (v : V)
    (_hV : 2 ≤ Fintype.card V) :
    (∑ f, if f ∈ onPathEv cf e v then ∏ i, Wt cf i (f i) else 0) ≤
    ENNReal.ofReal (cf.congestion / (Fintype.card V : ℝ) ^ 2) := by
  -- Apply the weighted union bound to the decomposition.
  have h_union_bound : (∑ f, if f ∈ onPathEv cf e v then ∏ i, Wt cf i (f i) else 0) ≤ ∑ p : DP V, (∑ f, if f ∈ onPathEvFixed cf e v p.val.1 p.val.2 p.prop then ∏ i, Wt cf i (f i) else 0) := by
    apply ennreal_weighted_union_bound;
    exact fun f hf => by obtain ⟨ a, b, h, hf ⟩ := onPathEv_subset_fixed cf e v f hf; exact ⟨ ⟨ ⟨ a, b ⟩, h ⟩, Finset.mem_univ _, hf ⟩ ;
  -- Apply the equality from onPathEvFixed_eq to each term in the sum.
  have h_eq : ∑ p : DP V, (∑ f, if f ∈ onPathEvFixed cf e v p.val.1 p.val.2 p.prop then ∏ i, Wt cf i (f i) else 0) = (Fintype.card V : ℝ≥0∞)⁻¹ * (Fintype.card V : ℝ≥0∞)⁻¹ * ∑ p : DP V, ∑ l ∈ (VPF cf p.val.1 p.val.2).filter (fun l => v ∈ l), (cf.flow l : ℝ≥0∞) := by
    rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => onPathEvFixed_eq cf e v _ _ _;
  -- Apply the bound from path_flow_through_le_vf to each term in the sum.
  have h_bound : ∑ p : DP V, ∑ l ∈ (VPF cf p.val.1 p.val.2).filter (fun l => v ∈ l), (cf.flow l : ℝ≥0∞) ≤ ENNReal.ofReal (cf.vertexFlow v) := by
    have h_bound : ∑ p : DP V, ∑ l ∈ (VPF cf p.val.1 p.val.2).filter (fun l => v ∈ l), (cf.flow l : ℝ) ≤ cf.vertexFlow v := by
      rw [ Finset.sum_sigma' ];
      refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
      rotate_left;
      exact Finset.biUnion ( Finset.univ : Finset ( DP V ) ) fun p => Finset.filter ( fun l => v ∈ l ) ( VPF cf p.val.1 p.val.2 );
      · simp +decide [ Finset.subset_iff ];
        exact fun l a b hab hl hv => ⟨ Finset.mem_filter.mp hl |>.1, hv ⟩;
      · exact fun _ _ _ => NNReal.coe_nonneg _;
      · refine' le_of_eq _;
        refine' Finset.sum_bij ( fun x _ => x.snd ) _ _ _ _ <;> simp +decide;
        · exact fun a ha hv => ⟨ ⟨ _, _, a.1.2, ha ⟩, hv ⟩;
        · simp +contextual [ VPF ];
          grind;
    convert ENNReal.ofReal_le_ofReal h_bound using 1;
    rw [ ENNReal.ofReal_sum_of_nonneg ];
    · simp +decide [ ENNReal.ofReal_sum_of_nonneg ];
    · exact fun _ _ => Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _;
  refine' le_trans h_union_bound ( h_eq.le.trans _ );
  refine' le_trans ( mul_le_mul_right h_bound _ ) _;
  rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
  · rw [ ENNReal.toReal_ofReal, ENNReal.toReal_ofReal ];
    · rw [ ← mul_inv, inv_eq_one_div, div_mul_eq_mul_div, div_le_div_iff₀ ] <;> first | positivity | nlinarith [ vertexFlow_le_congestion cf v ] ;
    · exact div_nonneg ( congestion_nonneg cf ) ( sq_nonneg _ );
    · exact Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _;
  · simp +decide [ ENNReal.mul_eq_top ]

/-
The ENNReal weighted sum of mipEv is bounded by C²(n+2|E|)/n⁴.
-/
private lemma mipEv_ennreal_bound (cf : ConcurrentFlow G) (e₁ e₂ : H.edgeFinset)
    (hne : e₁ ≠ e₂)
    (h1 : e₁.val.out.1 ≠ e₂.val.out.1) (h2 : e₁.val.out.1 ≠ e₂.val.out.2)
    (h3 : e₁.val.out.2 ≠ e₂.val.out.1) (h4 : e₁.val.out.2 ≠ e₂.val.out.2)
    (hV : 2 ≤ Fintype.card V) :
    (∑ f : ∀ i : Idx (W := W) (H := H) (V := V), Beta cf i,
      if f ∈ mipEv cf e₁ e₂ then ∏ i, Wt cf i (f i) else 0) ≤
    ENNReal.ofReal (cf.congestion ^ 2 *
      ((Fintype.card V : ℝ) + 2 * (G.edgeFinset.card : ℝ)) /
      (Fintype.card V : ℝ) ^ 4) := by
  refine' le_trans ( mipEv_subset_union cf e₁ e₂ hne h1 h2 h3 h4 |> fun h => ennreal_weighted_union_bound _ _ _ _ h ) _;
  -- Apply the independence theorem to factor the sum.
  have h_factor : ∀ p : V × V, (∑ f, if f ∈ onPathEv cf e₁ p.1 ∩ onPathEv cf e₂ p.2 then ∏ i, Wt cf i (f i) else 0) ≤ (ENNReal.ofReal (cf.congestion / (Fintype.card V : ℝ) ^ 2)) ^ 2 := by
    intro p
    have h_prod : (∑ f, if f ∈ onPathEv cf e₁ p.1 ∩ onPathEv cf e₂ p.2 then ∏ i, Wt cf i (f i) else 0) = (∑ f, if f ∈ onPathEv cf e₁ p.1 then ∏ i, Wt cf i (f i) else 0) * (∑ f, if f ∈ onPathEv cf e₂ p.2 then ∏ i, Wt cf i (f i) else 0) := by
      convert product_independence_thm ( fun i f => Wt cf i f ) ( wt_sum_one cf ) ( onPathEv cf e₁ p.1 ) ( onPathEv cf e₂ p.2 ) _ _ _ _ _ using 1;
      all_goals norm_cast;
      exact { Sum.inl e₁.val.out.1, Sum.inl e₁.val.out.2 } ∪ Finset.univ.image ( fun q : DP V => Sum.inr ⟨ e₁, q ⟩ );
      exact { Sum.inl e₂.val.out.1, Sum.inl e₂.val.out.2 } ∪ Finset.univ.image ( fun q : DP V => Sum.inr ⟨ e₂, q ⟩ );
      · exact edge_dep_disjoint e₁ e₂ hne h1 h2 h3 h4;
      · intro f₁ f₂ hf;
        exact onPathEv_dep cf e₁ p.1 f₁ f₂ fun i hi => hf i <| by aesop;
      · intro f₁ f₂ hf;
        convert onPathEv_dep cf e₂ p.2 f₁ f₂ _;
        grind;
    convert mul_le_mul' ( onPathEv_weighted_sum_le cf e₁ p.1 hV ) ( onPathEv_weighted_sum_le cf e₂ p.2 hV ) using 1 ; ring;
  refine' le_trans ( Finset.sum_le_sum fun p hp => h_factor p ) _;
  simp +decide [ mul_comm ];
  have h_card : (Finset.card (Finset.filter (fun p : V × V => p.1 = p.2 ∨ G.Adj p.1 p.2) Finset.univ)) ≤ (Fintype.card V : ℝ) + 2 * (G.edgeFinset.card : ℝ) := by
    norm_cast;
    refine' le_trans ( Finset.card_le_card _ ) _;
    exact Finset.image ( fun v => ( v, v ) ) Finset.univ ∪ Finset.biUnion G.edgeFinset ( fun e => Finset.image ( fun p => ( p.1, p.2 ) ) ( { ( e.out.1, e.out.2 ), ( e.out.2, e.out.1 ) } : Finset ( V × V ) ) );
    · simp +decide [ Finset.subset_iff ];
      rintro a b ( rfl | hab ) <;> [ exact Or.inl rfl; exact Or.inr ⟨ s(a, b), by simpa using hab, by
        have := Quot.out_eq ( s(a, b) );
        grind ⟩ ];
    · refine' le_trans ( Finset.card_union_le _ _ ) _;
      refine' add_le_add _ _;
      · exact Finset.card_image_le.trans_eq ( Finset.card_univ );
      · refine' le_trans ( Finset.card_biUnion_le ) _;
        simp +decide;
        exact le_trans ( Finset.sum_le_sum fun _ _ => Finset.card_insert_le _ _ ) ( by simp +decide [ mul_comm ] );
  rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
  · convert mul_le_mul_of_nonneg_left h_card ( sq_nonneg ( cf.congestion / ( Fintype.card V : ℝ ) ^ 2 ) ) using 1 ; ring_nf;
    · rw [ ENNReal.toReal_ofReal ( by exact mul_nonneg ( congestion_nonneg cf ) ( sq_nonneg _ ) ) ] ; ring;
    · rw [ ENNReal.toReal_ofReal ( by positivity ) ] ; ring;
  · exact ENNReal.mul_ne_top ( ENNReal.pow_ne_top ( ENNReal.ofReal_ne_top ) ) ( ENNReal.natCast_ne_top _ )

/-- Core measure bound: μ(mipEv) ≤ C²(|V|+2|E(G)|)/|V|⁴ -/
private lemma mipEv_measure_toReal_le (cf : ConcurrentFlow G) (e₁ e₂ : H.edgeFinset)
    (hne : e₁ ≠ e₂)
    (h1 : e₁.val.out.1 ≠ e₂.val.out.1) (h2 : e₁.val.out.1 ≠ e₂.val.out.2)
    (h3 : e₁.val.out.2 ≠ e₂.val.out.1) (h4 : e₁.val.out.2 ≠ e₂.val.out.2)
    (hV : 2 ≤ Fintype.card V) :
    letI : MeasurableSpace (∀ i : Idx (W := W) (H := H) (V := V), Beta cf i) := ⊤
    ((weightedPMF (fun f => ∏ i, Wt cf i (f i))
      (total_weight_ne_zero (Wt cf) (wt_sum_one cf))
      (total_weight_ne_top (Wt cf) (wt_sum_one cf))).toMeasure (mipEv cf e₁ e₂)).toReal ≤
    cf.congestion ^ 2 * ((Fintype.card V : ℝ) + 2 * (G.edgeFinset.card : ℝ)) /
      (Fintype.card V : ℝ) ^ 4 := by
  rw [prod_measure_eq (Wt cf) (wt_sum_one cf)]
  set S := ∑ f : ∀ i : Idx (W := W) (H := H) (V := V), Beta cf i,
    if f ∈ mipEv cf e₁ e₂ then ∏ i, Wt cf i (f i) else 0
  set R := cf.congestion ^ 2 * ((↑(Fintype.card V) : ℝ) + 2 * ↑G.edgeFinset.card) /
    (↑(Fintype.card V)) ^ 4
  have hR_nn : 0 ≤ R := by positivity
  have hbound := mipEv_ennreal_bound cf e₁ e₂ hne h1 h2 h3 h4 hV
  exact le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound)
                 (le_of_eq (ENNReal.toReal_ofReal hR_nn))

/-- The measure of the MIP event for non-incident edges is bounded by the congestion.
    This is the core probability bound from the LLL argument. -/
private lemma prob_bound_mip_noninc (cf : ConcurrentFlow G) (e₁ e₂ : H.edgeFinset)
    (_hlt : edgeLT e₁ e₂)
    (hne : e₁ ≠ e₂)
    (h1 : e₁.val.out.1 ≠ e₂.val.out.1) (h2 : e₁.val.out.1 ≠ e₂.val.out.2)
    (h3 : e₁.val.out.2 ≠ e₂.val.out.1) (h4 : e₁.val.out.2 ≠ e₂.val.out.2)
    (hcong : cf.congestion ≤
      (Fintype.card V : ℝ) ^ 2 /
        (15 * √ (H.edgeFinset.card : ℝ) * √ (G.edgeFinset.card : ℝ)))
    (hV : 2 ≤ Fintype.card V) (hn : 1796 < Fintype.card V)
    (hEH : 1 < H.edgeFinset.card)
    (h100 : 100 * H.edgeFinset.card < Fintype.card V) :
    letI : MeasurableSpace (∀ i : Idx (W := W) (H := H) (V := V), Beta cf i) := ⊤
    ((weightedPMF (fun f => ∏ i, Wt cf i (f i))
      (total_weight_ne_zero (Wt cf) (wt_sum_one cf))
      (total_weight_ne_top (Wt cf) (wt_sum_one cf))).toMeasure (mipEv cf e₁ e₂)).toReal ≤
    1 / (48 * H.edgeFinset.card + 52 : ℝ) := by
  exact le_trans (mipEv_measure_toReal_le cf e₁ e₂ hne h1 h2 h3 h4 hV)
    (mip_final_arith (Fintype.card V) H.edgeFinset.card G.edgeFinset.card cf.congestion
      hcong (congestion_nonneg cf) (cf_edge_count cf hV) h100 hEH hn hV)

/-- Canonical MIP events have probability ≤ 1/(48|E(H)|+52) by the congestion bound. -/
private lemma prob_bound_canonical_mip (cf : ConcurrentFlow G) (e₁ e₂ : H.edgeFinset)
    (hlt : edgeLT e₁ e₂)
    (hcong : cf.congestion ≤
      (Fintype.card V : ℝ) ^ 2 /
        (15 * √ (H.edgeFinset.card : ℝ) * √ (G.edgeFinset.card : ℝ)))
    (hV : 2 ≤ Fintype.card V) (hn : 1796 < Fintype.card V)
    (hEH : 1 < H.edgeFinset.card)
    (h100 : 100 * H.edgeFinset.card < Fintype.card V) :
    letI : MeasurableSpace (∀ i : Idx (W := W) (H := H) (V := V), Beta cf i) := ⊤
    ((weightedPMF (fun f => ∏ i, Wt cf i (f i))
      (total_weight_ne_zero (Wt cf) (wt_sum_one cf))
      (total_weight_ne_top (Wt cf) (wt_sum_one cf))).toMeasure (bEv cf (Sum.inr ⟨e₁, e₂⟩))).toReal ≤
    1 / (48 * H.edgeFinset.card + 52 : ℝ) := by
  simp only [bEv, hlt, if_pos]
  unfold mipEv
  by_cases hne : e₁ = e₂
  · simp [hne]; positivity
  · simp only [hne, if_neg, not_false_eq_true]
    by_cases h1 : e₁.val.out.1 = e₂.val.out.1
    · simp [h1]; positivity
    · simp only [h1, if_neg, not_false_eq_true]
      by_cases h2 : e₁.val.out.1 = e₂.val.out.2
      · simp [h2]; positivity
      · simp only [h2, if_neg, not_false_eq_true]
        by_cases h3 : e₁.val.out.2 = e₂.val.out.1
        · simp [h3]; positivity
        · simp only [h3, if_neg, not_false_eq_true]
          by_cases h4 : e₁.val.out.2 = e₂.val.out.2
          · simp [h4]; positivity
          · simp only [h4, if_neg, not_false_eq_true]
            convert prob_bound_mip_noninc cf e₁ e₂ hlt hne h1 h2 h3 h4
              hcong hV hn hEH h100 using 2
            unfold mipEv
            simp [hne, h1, h2, h3, h4]

/-- The probability of each bad event is bounded by 1/(48|E(H)|+52). -/
lemma prob_bound (cf : ConcurrentFlow G) (k : BIdx (W := W) (H := H))
    (hcong : cf.congestion ≤
      (Fintype.card V : ℝ) ^ 2 /
        (15 * √ (H.edgeFinset.card : ℝ) * √ (G.edgeFinset.card : ℝ)))
    (hV : 2 ≤ Fintype.card V) (hn : 1796 < Fintype.card V)
    (hEH : 1 < H.edgeFinset.card)
    (h100 : 100 * H.edgeFinset.card < Fintype.card V) :
    letI : MeasurableSpace (∀ i : Idx (W := W) (H := H) (V := V), Beta cf i) := ⊤
    ((weightedPMF (fun f => ∏ i, Wt cf i (f i))
      (total_weight_ne_zero (Wt cf) (wt_sum_one cf))
      (total_weight_ne_top (Wt cf) (wt_sum_one cf))).toMeasure (bEv cf k)).toReal ≤
    1 / (48 * H.edgeFinset.card + 52 : ℝ) := by
  cases k with
  | inl e => exact prob_bound_collision cf e hV hEH h100
  | inr p =>
    obtain ⟨e₁, e₂⟩ := p
    by_cases hlt : edgeLT e₁ e₂
    · exact prob_bound_canonical_mip cf e₁ e₂ hlt hcong hV hn hEH h100
    · exact prob_bound_noncanonical cf e₁ e₂ hlt hEH

/-
The number of edges incident to a vertex is at most 3 (subcubic).
-/
lemma incident_edges_le (hH : H.IsSubcubic) (v : W) :
    (Finset.univ.filter (fun e : H.edgeFinset =>
      e.val.out.1 = v ∨ e.val.out.2 = v)).card ≤ 3 := by
  convert hH v using 1;
  refine' Finset.card_bij ( fun e _ => if e.val.out.1 = v then e.val.out.2 else e.val.out.1 ) _ _ _ <;> simp +decide;
  · intro e he h; split_ifs <;> simp_all +decide ;
    · convert he using 1;
      rw [ ← SimpleGraph.mem_edgeSet ];
      simp +decide [ ← ‹ ( Quot.out e ).1 = v › ];
    · grind +suggestions;
  · intro a ha ha' b hb hb' hab;
    rw [ ← Quot.out_eq a, ← Quot.out_eq b ];
    grind;
  · intro w hw; use s(v, w); simp +decide [ hw ] ;
    have := Quot.out_eq ( s(v, w) : Sym2 W );
    grind

/-- The number of collision events with v in their bVertices. -/
lemma collision_events_through_vertex (hH : H.IsSubcubic) (v : W) :
    (Finset.univ.filter (fun e : H.edgeFinset =>
      v ∈ bVertices (Sum.inl e : BIdx (W := W) (H := H)))).card ≤ 3 := by
  convert incident_edges_le hH v using 2
  ext e; simp [bVertices, Finset.mem_insert, Finset.mem_singleton]; tauto

/-
Each edge is in at most |E(H)| canonical pairs.
-/
lemma canonical_pairs_per_edge (e : H.edgeFinset) :
    (Finset.univ.filter (fun p : H.edgeFinset × H.edgeFinset =>
      edgeLT p.1 p.2 ∧ (p.1 = e ∨ p.2 = e))).card ≤ H.edgeFinset.card := by
  -- Consider the function $f$ that maps a pair $(p_1, p_2)$ to $p_2$.
  set f : H.edgeFinset × H.edgeFinset → H.edgeFinset := fun p => if p.1 = e then p.2 else p.1;
  have h_inj : Set.InjOn f {p : H.edgeFinset × H.edgeFinset | edgeLT p.1 p.2 ∧ (p.1 = e ∨ p.2 = e)} := by
    intro p hp q hq; simp +decide [ f ] at *;
    have h_antisymm : ∀ (a b : H.edgeFinset), edgeLT a b → ¬edgeLT b a := by
      exact fun a b hab => @lt_asymm _ edgeFinsetLinearOrder.toPreorder a b hab;
    grind;
  have h_card : Finset.card (Finset.image f (Finset.filter (fun p : H.edgeFinset × H.edgeFinset => edgeLT p.1 p.2 ∧ (p.1 = e ∨ p.2 = e)) Finset.univ)) ≤ Finset.card (Finset.univ : Finset H.edgeFinset) := by
    exact Finset.card_le_univ _;
  rw [ Finset.card_image_of_injOn ] at h_card;
  · exact h_card.trans ( by simp +decide );
  · convert h_inj using 1;
    grind

lemma degree_bound (hH : H.IsSubcubic)
    (k : BIdx (W := W) (H := H)) :
    (bGamma k).card ≤ 12 * H.edgeFinset.card + 12 := by
  -- Let's define the collision part and the canonical MIP part.
  set collision_part := Finset.univ.filter (fun k' => ∃ e : H.edgeFinset, k' = Sum.inl e ∧ ¬Disjoint (bVertices k) (bVertices k'))
  set mip_part := Finset.univ.filter (fun k' => ∃ e₁ e₂ : H.edgeFinset, k' = Sum.inr (e₁, e₂) ∧ edgeLT e₁ e₂ ∧ ¬Disjoint (bVertices k) (bVertices k'));
  -- By definition of $bGamma$, we know that $bGamma k \subseteq collision_part \cup mip_part$.
  have h_subset : bGamma k ⊆ collision_part ∪ mip_part := by
    intro k' hk';
    rcases k' with ( _ | ⟨ e₁, e₂ ⟩ ) <;> simp_all +decide [ bGamma ];
    · exact Or.inl ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, _, rfl, hk'.2 ⟩ );
    · by_cases h : edgeLT e₁ e₂ <;> simp_all +decide [ bVertices ];
      exact Or.inr ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, e₁, e₂, rfl, h, by
        rcases k with ( _ | ⟨ e₁', e₂' ⟩ ) <;> simp_all +decide [ bVertices ];
        grind ⟩ );
  -- By definition of $collision_part$, we know that $|collision_part| \leq 12$.
  have h_collision_part : collision_part.card ≤ 12 := by
    -- By definition of $collision_part$, we know that $|collision_part| \leq |R|$.
    have h_collision_part_card : collision_part.card ≤ (Finset.univ.filter (fun e : H.edgeFinset => ∃ v ∈ bVertices k, e.val.out.1 = v ∨ e.val.out.2 = v)).card := by
      refine' le_trans ( Finset.card_le_card _ ) _;
      exact Finset.image ( fun e : H.edgeFinset => Sum.inl e ) ( Finset.univ.filter ( fun e : H.edgeFinset => ∃ v ∈ bVertices k, e.val.out.1 = v ∨ e.val.out.2 = v ) );
      · intro k' hk'
        obtain ⟨e, he₁, he₂⟩ := Finset.mem_filter.mp hk' |>.2
        simp [he₁] at he₂ ⊢
        generalize_proofs at *;
        contrapose! he₂; simp_all +decide [ Finset.disjoint_left ] ;
        intro v hv; specialize he₂ v hv; simp_all +decide [ bVertices ] ;
        exact ⟨ Ne.symm he₂.1, Ne.symm he₂.2 ⟩;
      · exact Finset.card_image_le;
    refine' le_trans h_collision_part_card _;
    have h_card_bVertices : (bVertices k).card ≤ 4 := by
      rcases k with ( _ | ⟨ e₁, e₂ ⟩ ) <;> simp +decide [ bVertices ];
      · exact le_trans ( Finset.card_insert_le _ _ ) ( by norm_num );
      · grind +splitImp;
    have h_card_edges : ∀ v ∈ bVertices k, (Finset.univ.filter (fun e : H.edgeFinset => e.val.out.1 = v ∨ e.val.out.2 = v)).card ≤ 3 := by
      intro v hv
      apply incident_edges_le hH v;
    have h_card_edges : (Finset.univ.filter (fun e : H.edgeFinset => ∃ v ∈ bVertices k, e.val.out.1 = v ∨ e.val.out.2 = v)).card ≤ ∑ v ∈ bVertices k, (Finset.univ.filter (fun e : H.edgeFinset => e.val.out.1 = v ∨ e.val.out.2 = v)).card := by
      have h_card_edges : (Finset.univ.filter (fun e : H.edgeFinset => ∃ v ∈ bVertices k, e.val.out.1 = v ∨ e.val.out.2 = v)) ⊆ Finset.biUnion (bVertices k) (fun v => Finset.univ.filter (fun e : H.edgeFinset => e.val.out.1 = v ∨ e.val.out.2 = v)) := by
        simp +contextual [ Finset.subset_iff ];
      exact le_trans ( Finset.card_le_card h_card_edges ) ( Finset.card_biUnion_le );
    exact h_card_edges.trans ( le_trans ( Finset.sum_le_sum ‹_› ) ( by norm_num; linarith ) );
  -- By definition of $mip_part$, we know that $|mip_part| \leq 12 * |E(H)|$.
  have h_mip_part : mip_part.card ≤ 12 * H.edgeFinset.card := by
    -- By definition of $mip_part$, we know that $|mip_part| \leq \sum_{e \in R} |canonical_pairs_containing_e|$.
    have h_mip_part_le_sum : mip_part.card ≤ ∑ e ∈ Finset.filter (fun e : H.edgeFinset => ¬Disjoint (bVertices k) (bVertices (Sum.inl e : BIdx (W := W) (H := H)))) Finset.univ, (Finset.filter (fun p : H.edgeFinset × H.edgeFinset => edgeLT p.1 p.2 ∧ (p.1 = e ∨ p.2 = e)) Finset.univ).card := by
      have h_mip_part_le_sum : mip_part ⊆ Finset.biUnion (Finset.filter (fun e : H.edgeFinset => ¬Disjoint (bVertices k) (bVertices (Sum.inl e : BIdx (W := W) (H := H)))) Finset.univ) (fun e => Finset.image (fun p : H.edgeFinset × H.edgeFinset => Sum.inr
 p) (Finset.filter (fun p : H.edgeFinset × H.edgeFinset => edgeLT p.1 p.2 ∧ (p.1 = e ∨ p.2 = e)) Finset.univ)) := by
        simp +decide [ Finset.subset_iff, mip_part ];
        rintro a ha b hb c hc d hd rfl rfl h₁ h₂;
        contrapose! h₂;
        simp +decide [ bVertices, h₁ ];
        cases k <;> simp +decide [ bVertices ] at h₂ ⊢; all_goals grind;
      refine' le_trans ( Finset.card_le_card h_mip_part_le_sum ) _;
      refine' le_trans ( Finset.card_biUnion_le ) _;
      exact Finset.sum_le_sum fun _ _ => Finset.card_image_le;
    refine' le_trans h_mip_part_le_sum ( le_trans ( Finset.sum_le_sum fun e he => canonical_pairs_per_edge e ) _ );
    simp +zetaDelta at *;
    refine' Nat.mul_le_mul_right _ _;
    convert h_collision_part using 1;
    refine' Finset.card_bij ( fun x hx => Sum.inl x ) _ _ _ <;> simp +decide;
    · exact fun a ha ha' => ⟨ ha, ha' ⟩;
    · exact fun a ha x hx hax h => ⟨ ha, h ⟩;
  exact le_trans ( Finset.card_le_card h_subset ) ( by linarith [ Finset.card_union_le collision_part mip_part ] )

lemma lll_arith (_hEH : 1 < H.edgeFinset.card) (_hn : 1796 < Fintype.card V)
    (_h100 : 100 * H.edgeFinset.card < Fintype.card V) :
    4 * (1 / (48 * (H.edgeFinset.card : ℝ) + 52)) *
      ((12 * (H.edgeFinset.card : ℝ) + 12) + 1) ≤ 1 := by
  rw [ mul_one_div, div_mul_eq_mul_div, div_le_iff₀ ] <;> nlinarith only [ show ( H.edgeFinset.card : ℝ ) ≥ 2 by norm_cast ]

/-! ### MutuallyInducedPaths is symmetric -/

lemma mip_symm (l₁ l₂ : List V) :
    MutuallyInducedPaths G l₁ l₂ ↔ MutuallyInducedPaths G l₂ l₁ := by
  constructor <;> intro ⟨hd, ha⟩
  · exact ⟨Disjoint.symm hd, fun v₂ hv₂ v₁ hv₁ h => ha v₁ hv₁ v₂ hv₂ (G.adj_comm v₂ v₁ |>.mp h)⟩
  · exact ⟨Disjoint.symm hd, fun v₁ hv₁ v₂ hv₂ h => ha v₂ hv₂ v₁ hv₁ (G.adj_comm v₁ v₂ |>.mp h)⟩

/-! ### Main Theorem -/

set_option maxHeartbeats 6400000 in
theorem path_table_lll
    (hH : H.IsSubcubic)
    (cf : ConcurrentFlow G)
    (hcong : cf.congestion ≤
      (Fintype.card V : ℝ) ^ 2 /
        (15 * √ (H.edgeFinset.card : ℝ) * √ (G.edgeFinset.card : ℝ)))
    (hEH : 1 < H.edgeFinset.card)
    (hV : 2 ≤ Fintype.card V)
    (hn : 1796 < Fintype.card V)
    (h100 : 100 * H.edgeFinset.card < Fintype.card V) :
    ∃ (φ : W → V) (pathChoice : H.edgeFinset → List V),
      (∀ e : H.edgeFinset, pathChoice e ∈ cf.support) ∧
      (∀ e : H.edgeFinset,
        (pathChoice e).head? = some (φ (e.val.out.1)) ∧
        (pathChoice e).getLast? = some (φ (e.val.out.2))) ∧
      (∀ e₁ e₂ : H.edgeFinset, e₁ ≠ e₂ →
        (e₁.val.out.1 ≠ e₂.val.out.1) → (e₁.val.out.1 ≠ e₂.val.out.2) →
        (e₁.val.out.2 ≠ e₂.val.out.1) → (e₁.val.out.2 ≠ e₂.val.out.2) →
        MutuallyInducedPaths G (pathChoice e₁) (pathChoice e₂)) := by
  by_contra! h_contra
  have h_apply_lll : ∃ f : ∀ i : Idx (W := W) (H := H) (V := V), Beta cf i,
      0 < (∏ i, Wt cf i (f i)) ∧ ∀ k : BIdx (W := W) (H := H), f ∉ bEv cf k := by
    haveI : Nonempty (BIdx (W := W) (H := H)) :=
      ⟨Sum.inl ⟨Classical.choose (Finset.card_pos.mp (pos_of_gt hEH)),
        Classical.choose_spec (Finset.card_pos.mp (pos_of_gt hEH))⟩⟩
    have := @combinatorial_lll
      (∀ i : Idx (W := W) (H := H) (V := V), Beta cf i) _
      (BIdx (W := W) (H := H)) _ _ _
      (fun f => ∏ i, Wt cf i (f i))
      (total_weight_ne_zero (Wt cf) (wt_sum_one cf))
      (total_weight_ne_top (Wt cf) (wt_sum_one cf))
      (bEv cf) bGamma bGamma_self
      (p := 1 / (48 * H.edgeFinset.card + 52 : ℝ)) (by positivity)
      (d := 12 * H.edgeFinset.card + 12)
      (fun k => prob_bound cf k hcong hV hn hEH h100)
      (fun k => degree_bound hH k)
      (by exact_mod_cast lll_arith hEH hn h100)
      (by convert product_lopsidependence (Wt cf) (wt_sum_one (G := G) cf) (bEv cf) (bDep (V := V))
            (bDep_spec cf) bGamma bGamma_self bGamma_disjoint using 1;
          infer_instance)
    exact this
  obtain ⟨f, hf_pos, hf_not_in_bEv⟩ := h_apply_lll
  set φ : W → V := fun w => getV cf f w
  set pathChoice : H.edgeFinset → List V := fun e => f (Sum.inr ⟨e, ⟨(φ e.val.out.1, φ e.val.out.2), by
    intro h_eq
    exact hf_not_in_bEv (Sum.inl e) (by unfold bEv; exact Set.mem_setOf.mpr h_eq)⟩⟩) |>.val
  generalize_proofs at *
  refine' h_contra φ pathChoice _ _ |> fun ⟨e₁, e₂, he₁, he₂, he₃, he₄, he₅, he₆⟩ => he₆ _
  · intro e
    generalize_proofs at *
    exact Finset.mem_filter.mp (f (Sum.inr ⟨e, ⟨(φ e.val.out.1, φ e.val.out.2), by solve_by_elim⟩⟩) |>.2) |>.1
  · intro e
    have := f (Sum.inr ⟨e, ⟨(φ (Quot.out e.val).1, φ (Quot.out e.val).2), by
      grind⟩⟩) |>.2
    generalize_proofs at *
    exact Finset.mem_filter.mp this |>.2
  · -- Use canonical ordering to extract MIP condition
    have hne : e₁ ≠ e₂ := he₁
    rcases @lt_or_gt_of_ne _ edgeFinsetLinearOrder e₁ e₂ hne with h_lt | h_gt
    · -- e₁ < e₂ (canonical): use the event directly
      have h_ev := hf_not_in_bEv (Sum.inr ⟨e₁, e₂⟩)
      have : edgeLT e₁ e₂ := h_lt
      simp only [bEv, this, if_pos] at h_ev
      simp +decide [mipEv] at h_ev
      exact h_ev he₁ he₂ he₃ he₄ he₅ (by tauto) (by tauto)
    · -- e₂ < e₁ (non-canonical): use the symmetric event and MIP symmetry
      have h_ev := hf_not_in_bEv (Sum.inr ⟨e₂, e₁⟩)
      have hlt' : edgeLT e₂ e₁ := h_gt
      simp only [bEv, hlt', if_pos] at h_ev
      have : f ∉ mipEv cf e₂ e₁ := h_ev
      simp +decide [mipEv] at this
      exact (mip_symm _ _).mp
        (this (Ne.symm he₁) (Ne.symm he₂) he₄.symm he₃.symm (Ne.symm he₅) (by tauto) (by tauto))

end PathTableLLL
end
