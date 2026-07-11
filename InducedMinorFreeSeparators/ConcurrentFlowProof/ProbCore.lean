import Mathlib
import InducedMinorFreeSeparators.ConcurrentFlowProof.Defs
import InducedMinorFreeSeparators.ConcurrentFlowProof.CombLLL
import InducedMinorFreeSeparators.ConcurrentFlowProof.ProductIndep
import InducedMinorFreeSeparators.ConcurrentFlowProof.LLLProof
import InducedMinorFreeSeparators.ConcurrentFlowProof.ProbArg

open Finset SimpleGraph Real MeasureTheory
open scoped BigOperators NNReal ENNReal

noncomputable section

namespace SimpleGraph.ProbCore

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  {W : Type*} [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {H : SimpleGraph W} [DecidableRel H.Adj]

/-! ## Helper: connectivity from concurrent flow -/

omit [DecidableEq W] in
lemma edges_ge_of_cf (cf : ConcurrentFlow G) (_hV : 2 ≤ Fintype.card V) :
    Fintype.card V - 1 ≤ G.edgeFinset.card := by
  have h_path : ∀ s t : V, s ≠ t → G.Reachable s t := by
    intro s t hst
    obtain ⟨l, hl⟩ : ∃ l ∈ cf.support, l.head? = some s ∧ l.getLast? = some t := by
      contrapose! hst; have := cf.total_flow s t; simp_all +decide []
      exact Classical.not_not.1 fun h => absurd (this h)
        (by rw [Finset.sum_eq_zero fun l hl => by aesop]; norm_num)
    have := cf.valid l hl.1
    have h_path : ∀ {u v : V} {l : List V}, List.IsChain G.Adj l →
        l.head? = some u → l.getLast? = some v → G.Reachable u v := by
      intros u v l hl hu hv
      induction' l with u l ih generalizing u v <;> simp_all +decide []
      cases l <;> simp_all +decide []
      exact SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable hl.1) (ih rfl hv)
    exact h_path this.1 hl.2.1 hl.2.2
  have h_connected : G.Connected :=
    SimpleGraph.Connected.mk fun s t =>
      if h : s = t then h.symm ▸ SimpleGraph.Reachable.refl _ else h_path s t h
  obtain ⟨T, hT⟩ := h_connected.exists_isTree_le
  have := hT.2.card_edgeFinset
  exact Nat.sub_le_of_le_add
    (by linarith [show #T.edgeFinset ≤ #G.edgeFinset from Finset.card_mono <| by aesop])

/-! ## Helper: congestion lower bound -/

omit [DecidableRel G.Adj] in
lemma congestion_ge_two_mul (cf : ConcurrentFlow G) (hV : 2 ≤ Fintype.card V) :
    2 * ((Fintype.card V : ℝ) - 1) ≤ cf.congestion := by
  have h_vertex_flow : ∀ v : V, cf.vertexFlow v =
      ∑ l ∈ cf.support.filter (fun l => v ∈ l), (cf.flow l : ℝ) := by exact fun v => Eq.symm (ext_cauchy rfl)
  have h_total_flow : ∀ v : V, cf.vertexFlow v ≥
      (∑ t ∈ Finset.univ.erase v,
        ∑ l ∈ cf.support.filter (fun l => l.head? = some v ∧ l.getLast? = some t),
          (cf.flow l : ℝ)) +
      (∑ s ∈ Finset.univ.erase v,
        ∑ l ∈ cf.support.filter (fun l => l.head? = some s ∧ l.getLast? = some v),
          (cf.flow l : ℝ)) := by
    intro v; rw [h_vertex_flow]; rw [← Finset.sum_add_distrib]
    have h_split_sum : Finset.filter (fun l => v ∈ l) cf.support ⊇
        Finset.biUnion (Finset.univ.erase v) (fun t =>
          Finset.filter (fun l => l.head? = some v ∧ l.getLast? = some t) cf.support ∪
          Finset.filter (fun l => l.head? = some t ∧ l.getLast? = some v) cf.support) := by
      intro l hl; simp_all +decide []
      rcases hl with ⟨a, ha, hl | hl⟩ <;> simp_all +decide [List.mem_of_mem_head?]
      exact List.mem_of_mem_getLast? hl.2.2
    refine' le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg h_split_sum fun _ _ _ => by positivity)
    rw [Finset.sum_biUnion]
    · refine' Finset.sum_le_sum fun t ht => _
      rw [Finset.sum_union]; simp +contextual [Finset.disjoint_left]
      exact fun l hl hl' hl'' => by rintro rfl; exact Finset.notMem_erase _ _ ht
    · intro t ht t' ht' h; simp_all +decide [Finset.disjoint_left]; grind
  refine' le_trans _ (Finset.le_sup' (fun v => cf.vertexFlow v) (Finset.mem_univ (Classical.arbitrary V)))
  refine' le_trans _ (h_total_flow _)
  rw [Finset.sum_congr rfl fun t ht => cf.total_flow _ _ <| by aesop,
      Finset.sum_congr rfl fun t ht => cf.total_flow _ _ <| by aesop]
  norm_num [two_mul, hV]; rw [Nat.cast_pred (by linarith)]

/-! ## Arithmetic for contradiction case -/

private lemma arith_1800_bound (k : ℕ) (hk1 : 11 ≤ k) (hk2 : k ≤ 1795) :
    (k + 1 : ℝ) ^ 4 < 1800 * (k : ℝ) ^ 3 := by
      norm_cast; nlinarith only [ hk1, hk2, pow_pos ( by linarith : 0 < k ) 2, pow_pos ( by linarith : 0 < k ) 3 ] ;

omit [DecidableEq W] in
private lemma contradiction_case
    (cf : ConcurrentFlow G)
    (hcong : cf.congestion ≤
      (Fintype.card V : ℝ) ^ 2 /
        (15 * √ (H.edgeFinset.card : ℝ) * √ (G.edgeFinset.card : ℝ)))
    (hEH : 1 < H.edgeFinset.card)
    (hV : 2 ≤ Fintype.card V)
    (hn_ge : 11 < Fintype.card V)
    (hn_le : Fintype.card V ≤ 1796) :
    False := by
      have h_eG : (Fintype.card V - 1 : ℝ) ≤ G.edgeFinset.card := by
        convert edges_ge_of_cf cf hV using 1;
        rw [ ← @Nat.cast_le ℝ ] ; norm_num [ Nat.cast_sub ( show 1 ≤ Fintype.card V from by linarith ) ];
      have h_eH : (2 : ℝ) ≤ H.edgeFinset.card := by
        exact_mod_cast hEH;
      have h_cong_lb : 2 * ((Fintype.card V : ℝ) - 1) ≤ cf.congestion := by
        convert congestion_ge_two_mul cf hV using 1;
      have h_cong_le : cf.congestion ≤ (Fintype.card V : ℝ) ^ 2 / (15 * Real.sqrt 2 * Real.sqrt (Fintype.card V - 1)) := by
        refine le_trans hcong ?_;
        gcongr;
        exact mul_pos ( mul_pos ( by norm_num ) ( Real.sqrt_pos.mpr ( by norm_num ) ) ) ( Real.sqrt_pos.mpr ( by linarith [ show ( Fintype.card V : ℝ ) ≥ 12 by norm_cast ] ) );
      have h_cong_le_sq : (2 * ((Fintype.card V : ℝ) - 1)) ^ 2 ≤ ((Fintype.card V : ℝ) ^ 2 / (15 * Real.sqrt 2 * Real.sqrt (Fintype.card V - 1))) ^ 2 := by
        exact pow_le_pow_left₀ ( mul_nonneg zero_le_two ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( by linarith ) ) ) ) ( h_cong_lb.trans h_cong_le ) _;
      norm_num [ mul_pow, div_pow ] at h_cong_le_sq;
      rw [ Real.sq_sqrt ( sub_nonneg_of_le ( mod_cast hV.trans' ( by norm_num ) ) ), le_div_iff₀ ] at h_cong_le_sq <;> nlinarith only [ h_cong_le_sq, show ( Fintype.card V : ℝ ) ≥ 12 by exact_mod_cast hn_ge, show ( Fintype.card V : ℝ ) ≤ 1796 by exact_mod_cast hn_le, pow_pos ( show ( Fintype.card V : ℝ ) > 0 by positivity ) 3, pow_pos ( show ( Fintype.card V : ℝ ) > 0 by positivity ) 4 ]

/-! ## LLL case: n ≥ 1797 -/

omit [DecidableEq W] in
private lemma edge_bound_from_congestion
    (cf : ConcurrentFlow G)
    (hcong : cf.congestion ≤
      (Fintype.card V : ℝ) ^ 2 /
        (15 * √ (H.edgeFinset.card : ℝ) * √ (G.edgeFinset.card : ℝ)))
    (hEH : 1 < H.edgeFinset.card)
    (hV : 2 ≤ Fintype.card V)
    (hn : 1796 < Fintype.card V) :
    (900 : ℝ) * H.edgeFinset.card * (Fintype.card V - 1) ^ 3 ≤
      (Fintype.card V : ℝ) ^ 4 := by
  have h_cong : (2 : ℝ) * ((Fintype.card V : ℝ) - 1) ≤ cf.congestion := by
    exact congestion_ge_two_mul cf hV;
  have h_edges : (Fintype.card V - 1 : ℝ) ≤ G.edgeFinset.card := by
    norm_cast;
    rw [ Int.subNatNat_of_le ( by linarith ) ] ; norm_cast ; exact edges_ge_of_cf cf hV;
  have h_combined : (2 * ((Fintype.card V : ℝ) - 1)) * (15 * Real.sqrt (H.edgeFinset.card : ℝ) * Real.sqrt ((Fintype.card V - 1 : ℝ))) ≤ (Fintype.card V : ℝ) ^ 2 := by
    rw [ le_div_iff₀ ] at hcong;
    · refine' le_trans _ hcong;
      gcongr;
      exact le_trans ( mul_nonneg zero_le_two ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( by linarith ) ) ) ) h_cong;
    · exact mul_pos ( mul_pos ( by norm_num ) ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( pos_of_gt hEH ) ) ) ) ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( pos_of_gt ( show 0 < #G.edgeFinset from Nat.pos_of_ne_zero ( by rintro h; norm_num [ h ] at *; linarith ) ) ) ) );
  convert pow_le_pow_left₀ ( by exact mul_nonneg ( mul_nonneg zero_le_two ( sub_nonneg.mpr <| Nat.one_le_cast.mpr <| by linarith ) ) <| mul_nonneg ( mul_nonneg ( by norm_num ) <| Real.sqrt_nonneg _ ) <| Real.sqrt_nonneg _ ) h_combined 2 using 1 ; ring_nf ; norm_num [ mul_assoc, mul_comm, mul_left_comm, pow_three, pow_two ] ; ring_nf;
  · rw [ Real.sq_sqrt ] <;> linarith [ show ( Fintype.card V : ℝ ) ≥ 1797 by norm_cast ];
  · ring

omit [Nonempty V] [DecidableEq W] [DecidableRel G.Adj] in
private lemma exists_good_assignment_given_phi
    (cf : ConcurrentFlow G)
    (φ : W → V)
    (hφ : ∀ e : H.edgeFinset, φ (e.val.out.1) ≠ φ (e.val.out.2)) :
    ∃ (pathChoice : H.edgeFinset → List V),
      (∀ e : H.edgeFinset, pathChoice e ∈ cf.support) ∧
      (∀ e : H.edgeFinset,
        (pathChoice e).head? = some (φ (e.val.out.1)) ∧
        (pathChoice e).getLast? = some (φ (e.val.out.2))) := by
  have h_exists_path : ∀ e : H.edgeFinset, ∃ l ∈ cf.support, l.head? = some (φ (e.val.out.1)) ∧ l.getLast? = some (φ (e.val.out.2)) := by
    exact fun e => by obtain ⟨ l, hl₁, hl₂, hl₃, hl₄ ⟩ := SimpleGraph.LLLProof.exists_path_st cf ( φ e.val.out.1 ) ( φ e.val.out.2 ) ( hφ e ) ; exact ⟨ l, hl₁, hl₂, hl₃ ⟩ ;
  exact ⟨ fun e => Classical.choose ( h_exists_path e ), fun e => Classical.choose_spec ( h_exists_path e ) |>.1, fun e => Classical.choose_spec ( h_exists_path e ) |>.2 ⟩

/-! ## Key bound: 56eH < n for n > 1796 -/

omit [DecidableEq W] in
private lemma eH_lt_n_div_100
    (cf : ConcurrentFlow G)
    (hcong : cf.congestion ≤
      (Fintype.card V : ℝ) ^ 2 /
        (15 * √ (H.edgeFinset.card : ℝ) * √ (G.edgeFinset.card : ℝ)))
    (hEH : 1 < H.edgeFinset.card)
    (hV : 2 ≤ Fintype.card V)
    (hn : 1796 < Fintype.card V) :
    100 * H.edgeFinset.card < Fintype.card V := by
  contrapose! hn with hn;
  have := edge_bound_from_congestion cf hcong hEH hV;
  exact not_lt.1 fun contra => absurd ( this contra ) ( by nlinarith only [ show ( Fintype.card V : ℝ ) ≥ 1797 by exact_mod_cast contra, show ( H.edgeFinset.card : ℝ ) ≥ 2 by exact_mod_cast hEH, show ( Fintype.card V : ℝ ) ≤ 100 * H.edgeFinset.card by exact_mod_cast hn, pow_pos ( by linarith [ ( by norm_cast : ( 1796 :ℝ ) < Fintype.card V ) ] : 0 < ( Fintype.card V :ℝ ) - 1 ) 2, pow_pos ( by linarith [ ( by norm_cast : ( 1796 :ℝ ) < Fintype.card V ) ] : 0 < ( Fintype.card V :ℝ ) - 1 ) 3 ] )

/-! ## Probabilistic existence of φ with distinct endpoints -/

private lemma exists_phi_distinct
    (hcard : H.edgeFinset.card < Fintype.card V) :
    ∃ φ : W → V, ∀ e : H.edgeFinset, φ (e.val.out.1) ≠ φ (e.val.out.2) := by
  contrapose! hcard;
  have h_bad_pairs : (Fintype.card V) ^ (Fintype.card W) ≤ H.edgeFinset.card * (Fintype.card V) ^ (Fintype.card W - 1) := by
    have h_bad_pairs : (Finset.univ : Finset (W → V)).sum (fun φ => (Finset.filter (fun e : H.edgeFinset => φ (e.val.out.1) = φ (e.val.out.2)) Finset.univ).card) ≥ (Fintype.card V) ^ (Fintype.card W) := by
      exact le_trans ( by simp +decide ) ( Finset.sum_le_sum fun φ _ => Finset.card_pos.mpr ⟨ Classical.choose ( hcard φ ), Finset.mem_filter.mpr ⟨ Finset.mem_univ _, Classical.choose_spec ( hcard φ ) ⟩ ⟩ );
    refine' le_trans h_bad_pairs _;
    have h_bad_pairs : ∀ e : H.edgeFinset, (Finset.univ : Finset (W → V)).sum (fun φ => if φ (e.val.out.1) = φ (e.val.out.2) then 1 else 0) ≤ (Fintype.card V) ^ (Fintype.card W - 1) := by
      intro e
      have h_bad_pairs : Finset.card (Finset.filter (fun φ : W → V => φ (e.val.out.1) = φ (e.val.out.2)) Finset.univ) ≤ (Fintype.card V) ^ (Fintype.card W - 1) := by
        have h_image : Finset.card (Finset.image (fun φ : W → V => fun w : {w : W | w ≠ e.val.out.1} => φ w) (Finset.filter (fun φ : W → V => φ (e.val.out.1) = φ (e.val.out.2)) Finset.univ)) ≤ (Fintype.card V) ^ (Fintype.card W - 1) := by
          refine' le_trans ( Finset.card_le_univ _ ) _;
          simp +decide [ Fintype.card_subtype_compl ];
        rwa [ Finset.card_image_of_injOn ] at h_image;
        intro φ hφ hψ h_eq h; ext w; by_cases hw : w = e.val.out.1 <;> simp_all +decide [ funext_iff ] ;
        have := Quot.out_eq ( e : Sym2 W ) ; rcases this' : Quot.out ( e : Sym2 W ) with ⟨ a, b ⟩ ; aesop;
      aesop;
    convert Finset.sum_le_sum fun e _ => h_bad_pairs e using 1;
    rw [ Finset.sum_comm ];
    exacts [ Finset.sum_congr rfl fun _ _ => by rw [ Finset.card_filter ], by simp +decide ];
  rcases n : Fintype.card W with ( _ | _ | n ) <;> simp_all +decide [ pow_succ' ];
  · rw [ Fintype.card_eq_zero_iff ] at n ; aesop;
  · exact le_of_mul_le_mul_right h_bad_pairs ( by positivity )

/-! ## LLL application: joint sampling of φ and paths

This is Lemma 4.3 from Korhonen–Lokshtanov [KL24]. The proof uses the
Lovász Local Lemma applied to a product distribution over edges of H.

**Proof outline (mathematical):**

For each edge e of H, independently sample:
  - (a, b) ∈ V × V uniformly at random
  - a path l from a to b from the concurrent flow (weighted by flow)

This defines a product measure over H.edgeFinset, where each coordinate
β(e) consists of valid (source, target, path) triples with weight
proportional to cf.flow(l) / (n·(n-1)).

The bad events are MIP failures for non-incident edge pairs with
all 4 W-vertices distinct. Each event depends on exactly 2 coordinates.
The probability of each bad event is bounded by:
  P ≤ (n + 2|E(G)|) · C² / (n·(n-1))² ≤ 1/(56·|E(H)|)

where C is the congestion. The dependency degree is ≤ 2·|E(H)|
(since each edge participates in at most |E(H)|-1 event pairs).
The symmetric LLL condition 4·p·(d+1) ≤ 1 gives:
  4/(56·|E(H)|) · (2·|E(H)|+1) ≈ 8/56 = 1/7 < 1.

The product_lll theorem then gives per-edge (a_e, b_e, l_e) triples
with MIP for all non-incident pairs. We define φ(w) using any incident
edge's endpoint assignment and use the corresponding paths as pathChoice.

**Note:** The consistency of φ across incident edges is handled by
the fact that MIP is only required for edges with all 4 W-vertices
distinct (non-incident edges). For incident edges sharing a vertex w,
we define φ(w) from one reference edge and adjust the other edges' paths
using Classical.choice from the concurrent flow.
-/
private lemma lll_case
    (hH : H.IsSubcubic)
    (cf : ConcurrentFlow G)
    (hcong : cf.congestion ≤
      (Fintype.card V : ℝ) ^ 2 /
        (15 * √ (H.edgeFinset.card : ℝ) * √ (G.edgeFinset.card : ℝ)))
    (hEH : 1 < H.edgeFinset.card)
    (hV : 2 ≤ Fintype.card V)
    (hn : 1796 < Fintype.card V) :
    ∃ (φ : W → V) (pathChoice : H.edgeFinset → List V),
      (∀ e : H.edgeFinset, pathChoice e ∈ cf.support) ∧
      (∀ e : H.edgeFinset,
        (pathChoice e).head? = some (φ (e.val.out.1)) ∧
        (pathChoice e).getLast? = some (φ (e.val.out.2))) ∧
      (∀ e₁ e₂ : H.edgeFinset, e₁ ≠ e₂ →
        (e₁.val.out.1 ≠ e₂.val.out.1) → (e₁.val.out.1 ≠ e₂.val.out.2) →
        (e₁.val.out.2 ≠ e₂.val.out.1) → (e₁.val.out.2 ≠ e₂.val.out.2) →
        MutuallyInducedPaths G (pathChoice e₁) (pathChoice e₂)) := by
  exact SimpleGraph.ProbArg.lll_main hH cf hcong hEH hV hn
    (eH_lt_n_div_100 cf hcong hEH hV hn)

/-! ## Main lemma -/

lemma exists_good_from_lll
    (hH : H.IsSubcubic)
    (cf : ConcurrentFlow G)
    (hcong : cf.congestion ≤
      (Fintype.card V : ℝ) ^ 2 /
        (15 * √ (H.edgeFinset.card : ℝ) * √ (G.edgeFinset.card : ℝ)))
    (hEH : 1 < H.edgeFinset.card)
    (hV : 2 ≤ Fintype.card V)
    (hn : 11 < Fintype.card V) :
    ∃ (φ : W → V) (pathChoice : H.edgeFinset → List V),
      (∀ e : H.edgeFinset, pathChoice e ∈ cf.support) ∧
      (∀ e : H.edgeFinset,
        (pathChoice e).head? = some (φ (e.val.out.1)) ∧
        (pathChoice e).getLast? = some (φ (e.val.out.2))) ∧
      (∀ e₁ e₂ : H.edgeFinset, e₁ ≠ e₂ →
        (e₁.val.out.1 ≠ e₂.val.out.1) → (e₁.val.out.1 ≠ e₂.val.out.2) →
        (e₁.val.out.2 ≠ e₂.val.out.1) → (e₁.val.out.2 ≠ e₂.val.out.2) →
        MutuallyInducedPaths G (pathChoice e₁) (pathChoice e₂)) := by
  by_cases h : Fintype.card V ≤ 1796
  · exact (contradiction_case cf hcong hEH hV hn h).elim
  · push_neg at h
    exact lll_case hH cf hcong hEH hV h

end SimpleGraph.ProbCore
