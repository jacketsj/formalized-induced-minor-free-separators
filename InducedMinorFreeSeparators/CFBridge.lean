/-
# Bridge between ConcurrentFlow and QDual

Connects the assumed KL result (congestion_lower_bound_of_no_induced_minor)
to the LP duality framework.
-/
import Mathlib
import InducedMinorFreeSeparators.ProofDefs
import InducedMinorFreeSeparators.ConcurrentFlow

open Finset BigOperators
open scoped NNReal

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Walk.support properties -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma walk_support_head' {u v : V} (p : G.Walk u v) :
    p.support.head? = some u := by
  cases p with
  | nil => simp [SimpleGraph.Walk.support]
  | cons _ _ => simp [SimpleGraph.Walk.support]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma walk_support_getLast' {u v : V} (p : G.Walk u v) :
    p.support.getLast? = some v := by
  induction p with
  | nil => simp [SimpleGraph.Walk.support]
  | cons _ p ih =>
    simp only [SimpleGraph.Walk.support]
    rw [List.getLast?_cons]
    simp [ih]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma walk_support_length_ge_two' {u v : V} (h : u ≠ v) (p : G.Walk u v) :
    2 ≤ p.support.length := by
  rw [p.length_support]
  cases p with
  | nil => exact absurd rfl h
  | cons _ p =>
    rw [SimpleGraph.Walk.length]
    omega

/-! ## vertexLoad ≥ 1 for vertices in support of nontrivial walk -/

omit [Fintype V] [DecidableRel G.Adj] in
lemma vertexLoad_pos_of_mem_support_of_pos_length
    {u v : V} (p : G.Walk u v) (hl : 0 < p.length)
    (x : V) (hx : x ∈ p.support) :
    1 ≤ SimpleGraph.Walk.vertexLoad x p := by
  induction' p with u v p ih generalizing x;
  · contradiction;
  · rename_i q hq;
    by_cases h : 0 < q.length <;> simp_all +decide [ SimpleGraph.Walk.vertexLoad ];
    · grind;
    · cases q <;> aesop

/-! ## ConcurrentFlow construction from a routing -/

noncomputable def routingCFSupport
    (_R : (u v : V) → G.Path u v → ℝ) : Finset (List V) :=
  (Finset.univ.biUnion fun u : V =>
    Finset.univ.biUnion fun v : V =>
      (Finset.univ : Finset (G.Path u v)).image
        fun (P : G.Path u v) => P.val.support).filter (fun l => 2 ≤ l.length)

noncomputable def routingCFFlowReal
    (R : (u v : V) → G.Path u v → ℝ) (l : List V) : ℝ :=
  ∑ u : V, ∑ v : V, ∑ P : G.Path u v,
    if (P : G.Walk u v).support = l ∧ u ≠ v then R u v P else 0

lemma routingCFFlowReal_nonneg
    (R : (u v : V) → G.Path u v → ℝ) (hR_nn : ∀ u v P, 0 ≤ R u v P)
    (l : List V) : 0 ≤ routingCFFlowReal (G := G) R l := by
  apply Finset.sum_nonneg; intro u _
  apply Finset.sum_nonneg; intro v _
  apply Finset.sum_nonneg; intro P _
  split_ifs with h
  · exact hR_nn u v P
  · exact le_refl 0

noncomputable def routingCFFlow
    (R : (u v : V) → G.Path u v → ℝ) (l : List V) : ℝ≥0 :=
  Real.toNNReal (routingCFFlowReal (G := G) R l)

lemma routingCFFlow_coe
    (R : (u v : V) → G.Path u v → ℝ) (hR_nn : ∀ u v P, 0 ≤ R u v P)
    (l : List V) :
    (routingCFFlow (G := G) R l : ℝ) = routingCFFlowReal (G := G) R l :=
  Real.coe_toNNReal _ (routingCFFlowReal_nonneg R hR_nn l)

/-
The routing flow for a path equals R u v P.
-/
lemma routingCFFlowReal_eq
    (R : (u v : V) → G.Path u v → ℝ)
    {u v : V} (huv : u ≠ v) (P : G.Path u v) :
    routingCFFlowReal (G := G) R P.val.support = R u v P := by
  unfold routingCFFlowReal;
  rw [ Finset.sum_eq_single u, Finset.sum_eq_single v ] <;> simp +contextual;
  · rw [ Finset.sum_eq_single P ] <;> simp +contextual [ huv ];
    grind +suggestions;
  · intro b hb;
    refine' Finset.sum_eq_zero fun x hx => if_neg _;
    intro h;
    have := walk_support_getLast' x.val; have := walk_support_getLast' P.val; simp_all +decide ;
  · intro b hb;
    refine' Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => _;
    have := walk_support_head' ( y : G.Walk b x ) ; have := walk_support_head' ( P : G.Walk u v ) ; aesop;

/-
Flow is zero outside the support.
-/
lemma routingCFFlow_zero_outside
    (R : (u v : V) → G.Path u v → ℝ) (_hR_nn : ∀ u v P, 0 ≤ R u v P)
    (l : List V) (hl : l ∉ routingCFSupport (G := G) R) :
    routingCFFlow (G := G) R l = 0 := by
  contrapose! hl;
  -- By definition of routingCFFlow, there exists some path P � such� that P.val.support = l � and� R u v P ≠ 0.
  obtain ⟨u, v, P, hP⟩ : ∃ u v : V, ∃ P : G.Path u v, P.val.support = l ∧ u ≠ v ∧ R u v P ≠ 0 := by
    contrapose! hl;
    unfold routingCFFlow;
    simp +decide;
    exact Finset.sum_nonpos fun u hu => Finset.sum_nonpos fun v hv => Finset.sum_nonpos fun P hP => by aesop;
  refine' Finset.mem_filter.mpr ⟨ _, _ ⟩;
  · aesop;
  · rw [ ← hP.1 ] ; exact walk_support_length_ge_two' hP.2.1 _;

/-
Total flow equals 1 for each pair.
-/
lemma routingCFFlow_total
    (R : (u v : V) → G.Path u v → ℝ) (hR_nn : ∀ u v P, 0 ≤ R u v P)
    (hR_sum : ∀ u v, ∑ P : G.Path u v, R u v P = 1)
    (s t : V) (hst : s ≠ t) :
    ∑ l ∈ (routingCFSupport (G := G) R).filter
        (fun l => l.head? = some s ∧ l.getLast? = some t),
      (routingCFFlow (G := G) R l : ℝ) = 1 := by
  convert hR_sum s t using 1;
  rw [ Finset.sum_subset ];
  any_goals exact Finset.image ( fun P : G.Path s t => P.val.support ) Finset.univ;
  · rw [ Finset.sum_image ];
    · refine' Finset.sum_congr rfl fun P _ => _;
      rw [ routingCFFlow_coe, routingCFFlowReal_eq ] <;> aesop;
    · intro P hP Q hQ h_eq;
      exact Subtype.ext ( SimpleGraph.Walk.ext_support h_eq );
  · intro l hl;
    simp +zetaDelta at *;
    unfold routingCFSupport at hl;
    grind +suggestions;
  · simp +contextual;
    intro a ha h; rw [ routingCFFlow_zero_outside ] ; aesop;
    exact fun h' => h h' ( walk_support_head' a ) ( walk_support_getLast' a )

/-
Paths in support are chains, nodup, length ≥ 2.
-/
lemma routingCFSupport_valid
    (R : (u v : V) → G.Path u v → ℝ)
    (l : List V) (hl : l ∈ routingCFSupport (G := G) R) :
    l.IsChain G.Adj ∧ l.Nodup ∧ 2 ≤ l.length := by
  obtain ⟨ u, v, P, hP ⟩ : ∃ u v : V, ∃ P : G.Path u v, l = P.val.support := by
    unfold routingCFSupport at hl; aesop;
  cases eq_or_ne u v <;> simp_all +decide;
  · unfold routingCFSupport at hl; aesop;
  · grind +suggestions

/-- Construct a ConcurrentFlow from a routing. -/
noncomputable def routingToCF [Nonempty V]
    (_hconn : G.Connected)
    (R : (u v : V) → G.Path u v → ℝ)
    (hR_nn : ∀ u v P, 0 ≤ R u v P)
    (hR_sum : ∀ u v, ∑ P : G.Path u v, R u v P = 1) :
    ConcurrentFlow G where
  support := routingCFSupport R
  valid := routingCFSupport_valid R
  flow := routingCFFlow R
  flow_support l hl := routingCFFlow_zero_outside R hR_nn l hl
  total_flow := routingCFFlow_total R hR_nn hR_sum

/-! ## Congestion comparison -/

lemma routingToCF_vertexFlow_le [Nonempty V]
    (hconn : G.Connected)
    (R : (u v : V) → G.Path u v → ℝ)
    (hR_nn : ∀ u v P, 0 ≤ R u v P)
    (hR_sum : ∀ u v, ∑ P : G.Path u v, R u v P = 1)
    (x : V) :
    (routingToCF hconn R hR_nn hR_sum).vertexFlow x ≤ routingCongestion R x := by
  unfold routingToCF;
  unfold ConcurrentFlow.vertexFlow routingCongestion; simp +decide [ routingCFFlow_coe, hR_nn ] ;
  -- By definition of `routingCFFlowReal`, we can rewrite the left-hand side of the inequality.
  have h_rewrite : ∑ l ∈ (routingCFSupport R).filter (fun l => x ∈ l), routingCFFlowReal R l = ∑ u, ∑ v, ∑ P : G.Path u v, if (P : G.Walk u v).support ∈ (routingCFSupport R).filter (fun l => x ∈ l) ∧ u ≠ v then R u v P else 0 := by
    unfold routingCFFlowReal;
    rw [ Finset.sum_comm, Finset.sum_congr rfl ];
    intro u hu;
    rw [ Finset.sum_comm, Finset.sum_congr rfl ];
    intro v hv;
    rw [ Finset.sum_comm, Finset.sum_congr rfl ];
    intro P hP; split_ifs <;> simp_all +decide [ Finset.sum_ite ] ;
  refine' h_rewrite.le.trans ( Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun v hv => Finset.sum_le_sum fun P hP => _ );
  split_ifs <;> simp_all +decide;
  · refine' le_mul_of_one_le_right ( hR_nn u v _ _ ) _;
    exact_mod_cast vertexLoad_pos_of_mem_support_of_pos_length _ ( by simpa using walk_support_length_ge_two' ( by tauto ) _ ) _ ( by tauto );
  · exact mul_nonneg ( hR_nn u v _ P.2 ) ( Nat.cast_nonneg _ )

lemma routingToCF_congestion_le [Nonempty V]
    (hconn : G.Connected)
    (R : (u v : V) → G.Path u v → ℝ)
    (hR_nn : ∀ u v P, 0 ≤ R u v P)
    (hR_sum : ∀ u v, ∑ P : G.Path u v, R u v P = 1) :
    (routingToCF hconn R hR_nn hR_sum).congestion ≤
      Finset.univ.sup' Finset.univ_nonempty (fun x => routingCongestion R x) := by
  unfold ConcurrentFlow.congestion
  apply Finset.sup'_le _ _ fun x _ => ?_
  exact le_trans (routingToCF_vertexFlow_le hconn R hR_nn hR_sum x)
    (Finset.le_sup' _ (Finset.mem_univ x))

/-! ## Main bridge -/

theorem QDual_ge_of_cf_bound [Nonempty V]
    (hconn : G.Connected)
    (C : ℝ)
    (hC : ∀ cf : ConcurrentFlow G, C < cf.congestion) :
    C ≤ QDual G := by
  apply le_csInf
  · have hpath : ∀ u v : V, Nonempty (G.Path u v) :=
      fun u v => ⟨(hconn u v).some.toPath⟩
    refine ⟨_, fun u v P => if P = (hpath u v).some then 1 else 0, ?_, ?_, rfl⟩
    · intro u v P; simp only; split_ifs <;> norm_num
    · intro u v; simp only; simp [Finset.sum_ite_eq', Finset.mem_univ]
  · rintro μ ⟨R, hR_nn, hR_sum, rfl⟩
    have h1 := routingToCF_congestion_le hconn R hR_nn hR_sum
    have h2 := hC (routingToCF hconn R hR_nn hR_sum)
    linarith

/-! ## HasInducedMinor → ContainsInducedMinor -/

theorem hasInducedMinor_imp_containsInducedMinor {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (h : HasInducedMinor G H) :
    G.ContainsInducedMinor H := by
  obtain ⟨φ⟩ := h
  refine ⟨φ.branch, ?_, φ.branch_connected, φ.branch_disjoint,
    φ.adj_preserved, φ.nonadj_preserved⟩
  intro w
  exact Set.nonempty_coe_sort.mp (φ.branch_connected w).nonempty

/-! ## oneSubdivision bounds -/

lemma subdivVertex_card_add_edges_le (h : ℕ) (hh : 2 ≤ h) :
    (Fintype.card (SubdivVertex h) : ℝ) +
      ↑((oneSubdivision h).edgeFinset.card) ≤ 2 * (h : ℝ) ^ 2 := by
  norm_cast;
  rw [ SimpleGraph.edgeFinset ];
  rw [ Set.toFinset_card ];
  rw [ Fintype.card_of_subtype ];
  case s => exact Finset.image ( fun p : KEdge h => Sym2.mk ( Sum.inl p.val.1, Sum.inr p ) ) ( Finset.univ : Finset ( KEdge h ) ) ∪ Finset.image ( fun p : KEdge h => Sym2.mk ( Sum.inl p.val.2, Sum.inr p ) ) ( Finset.univ : Finset ( KEdge h ) );
  · rw [ Finset.card_union_of_disjoint ];
    · rw [ Finset.card_image_of_injective, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
      · rw [ show Fintype.card ( KEdge h ) = h * ( h - 1 ) / 2 from ?_ ];
        · nlinarith [ Nat.div_mul_le_self ( h * ( h - 1 ) ) 2, Nat.sub_add_cancel ( by linarith : 1 ≤ h ) ];
        · convert Finset.card_filter ( fun p : Fin h × Fin h => p.1 < p.2 ) Finset.univ using 1;
          · refine' Finset.card_bij ( fun x hx => ( x.val.1, x.val.2 ) ) _ _ _ <;> aesop;
          · erw [ Finset.sum_product ] ; norm_num;
            simp +decide [ Finset.filter_lt_eq_Ioi ];
            exact Nat.div_eq_of_eq_mul_left zero_lt_two ( Nat.recOn h ( by norm_num ) fun n ih => by cases n <;> simp +decide [ Fin.sum_univ_succ, Nat.mul_succ ] at * ; linarith );
      · aesop;
      · aesop;
    · norm_num [ Finset.disjoint_left ];
      grind +revert;
  · rintro ⟨ u, v ⟩ ; rcases u with ( u | u ) <;> rcases v with ( v | v ) <;> simp +decide [ Sym2.eq_swap ] ;
    · exact fun h => by cases h;
    · exact ⟨ fun h => by cases h <;> [ exact Or.inl ( by tauto ) ; exact Or.inr ( by tauto ) ], fun h => by cases h <;> tauto ⟩;
    · exact ⟨ fun h => by cases h <;> tauto, fun h => by cases h <;> tauto ⟩;
    · exact fun h => by cases h;

lemma kl_constant_bound (h : ℕ) (hh : 2 ≤ h) :
    45 * Real.sqrt ((Fintype.card (SubdivVertex h) : ℝ) +
      ↑((oneSubdivision h).edgeFinset.card)) ≤ 64 * (h : ℝ) := by
  have hle := subdivVertex_card_add_edges_le h hh
  have hh_pos : (0 : ℝ) < h := by positivity
  calc 45 * Real.sqrt ((Fintype.card (SubdivVertex h) : ℝ) +
        ↑((oneSubdivision h).edgeFinset.card))
      ≤ 45 * Real.sqrt (2 * (h : ℝ) ^ 2) := by
        gcongr
    _ = 45 * ((h : ℝ) * Real.sqrt 2) := by
        congr 1
        rw [show 2 * (h : ℝ) ^ 2 = (h : ℝ) ^ 2 * 2 from by ring]
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hh_pos.le]
    _ = (45 * Real.sqrt 2) * (h : ℝ) := by ring
    _ ≤ 64 * (h : ℝ) := by
        gcongr
        have : Real.sqrt 2 ≤ 64 / 45 := by
          rw [Real.sqrt_le_left (by positivity)]
          norm_num
        linarith