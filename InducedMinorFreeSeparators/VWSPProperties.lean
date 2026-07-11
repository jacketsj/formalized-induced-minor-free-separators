/-
# VWSP Metric Properties

Properties of the VWSP shortest-path metric needed to apply the coarse pure pairs machinery:
- Optimal walks exist (the infimum distance is achieved)
- hG_ball: δ-connected sets have graph-connected δ/2-balls
- hG_path: shortest path existence with geodesic property
-/
import Mathlib
import InducedMinorFreeSeparators.VWSP
import InducedMinorFreeSeparators.CoarsePurePairs

open Set Function CoarsePurePairs SimpleGraph
open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Walk weight for dropUntil -/

/-
The heavy weight of a walk's suffix (dropUntil) is ≤ the total weight, for nonneg weights.
-/
omit [Fintype V] in
lemma edgeWeightSum_dropUntil_le {G : SimpleGraph V} {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) {u v : V} (p : G.Walk u v) {x : V} (hx : x ∈ p.support) :
    (p.dropUntil x hx).edgeWeightSum w ≤ p.edgeWeightSum w := by
  have h_split : p.edgeWeightSum w = (p.takeUntil x hx).edgeWeightSum w + (p.dropUntil x hx).edgeWeightSum w := by
    rw [ ← edgeWeightSum_append' ];
    rw [ SimpleGraph.Walk.take_spec ];
  linarith [ edgeWeightSum_nonneg hw ( p.takeUntil x hx ) ]

omit [Fintype V] in
/-- The light weight of a walk's suffix (dropUntil) is ≤ the total weight. -/
lemma edgeWeightSumLight_dropUntil_le {G : SimpleGraph V} {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) {u v : V} (p : G.Walk u v) {x : V} (hx : x ∈ p.support) :
    (p.dropUntil x hx).edgeWeightSumLight w ≤ p.edgeWeightSumLight w := by
  rw [edgeWeightSumLight_eq_half, edgeWeightSumLight_eq_half]
  exact div_le_div_of_nonneg_right (edgeWeightSum_dropUntil_le hw p hx) (by norm_num)

/-! ## Bypass weight bound -/

/-
The bypass of a walk has heavy weight ≤ the original walk's heavy weight.
-/
omit [Fintype V] in
lemma edgeWeightSum_bypass_le_vwsp {G : SimpleGraph V} {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) {u v : V} (p : G.Walk u v) :
    p.bypass.edgeWeightSum w ≤ p.edgeWeightSum w := by
  induction' p with u v p ih;
  · rfl;
  · by_cases h : v ∈ ( ‹G.Walk p ih›.bypass ).support <;> simp_all +decide [ SimpleGraph.Walk.bypass ];
    · refine' le_trans ( edgeWeightSum_dropUntil_le hw _ _ ) _;
      refine' le_trans ‹_› _;
      exact le_add_of_nonneg_left ( add_nonneg ( hw _ ) ( hw _ ) );
    · simp_all +decide [ SimpleGraph.Walk.edgeWeightSum ]

/-! ## Distance achieved by a path -/

/-
There exists a walk achieving the VWSP light distance.
-/
lemma weightedDistLight_achieved {G : SimpleGraph V} {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) (hconn : G.Connected) (u v : V) :
    ∃ (p : G.Walk u v), p.edgeWeightSumLight w = G.weightedDistLight w u v := by
  -- By definition of weighted distance, there exists a path $p$ from $u$ to $v$ such that $p.edgeWeightSum w = G.weightedDist w u v$.
  obtain ⟨p, hp⟩ : ∃ p : G.Walk u v, p.edgeWeightSum w = G.weightedDist w u v := by
    have h_nonempty : Set.Nonempty {p : G.Walk u v | ∀ q : G.Walk u v, p.edgeWeightSum w ≤ q.edgeWeightSum w} := by
      have h_finite : Set.Finite {p : G.Walk u v | p.length ≤ Fintype.card V} := by
        have h_finite_walks : ∀ n : ℕ, Set.Finite {p : G.Walk u v | p.length = n} := by
          intro n;
          exact Set.toFinite _;
        exact Set.Finite.subset ( Set.Finite.biUnion ( Set.finite_Iic ( Fintype.card V ) ) fun n hn => h_finite_walks n ) fun p hp => by aesop;
      obtain ⟨p, hp⟩ : ∃ p ∈ {p : G.Walk u v | p.length ≤ Fintype.card V}, ∀ q ∈ {p : G.Walk u v | p.length ≤ Fintype.card V}, p.edgeWeightSum w ≤ q.edgeWeightSum w := by
        apply_rules [ Set.exists_min_image ];
        have := hconn u v;
        obtain ⟨ p, hp ⟩ := this.exists_isPath;
        exact ⟨ p, by simpa using hp.length_lt.le ⟩;
      refine' ⟨ p, fun q => _ ⟩;
      have h_bypass : q.bypass.edgeWeightSum w ≤ q.edgeWeightSum w := by
        grind +suggestions;
      refine' le_trans ( hp.2 _ _ ) h_bypass;
      simp +zetaDelta at *;
      have := q.bypass_isPath;
      have := this.length_lt;
      linarith;
    obtain ⟨ p, hp ⟩ := h_nonempty;
    use p;
    exact le_antisymm ( le_csInf ⟨ _, ⟨ p, rfl ⟩ ⟩ fun q hq => by aesop ) ( csInf_le ⟨ 0, by rintro x ⟨ q, rfl ⟩ ; exact edgeWeightSum_nonneg hw _ ⟩ ⟨ p, rfl ⟩ );
  use p;
  rw [ weightedDistLight_eq_half, edgeWeightSumLight_eq_half, hp ]

/-
There exists a walk achieving the VWSP heavy distance.
-/
lemma weightedDist_achieved {G : SimpleGraph V} {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) (hconn : G.Connected) (u v : V) :
    ∃ (p : G.Walk u v), p.edgeWeightSum w = G.weightedDist w u v := by
  -- Apply the lemma weightedDist �Light�_achieved to find a walk p with edgeWeightSumLight w p = G.weightedDistLight w u v.
  obtain ⟨p, hp⟩ := weightedDistLight_achieved hw hconn u v;
  use p;
  convert congr_arg ( · * 2 ) hp using 1 <;> norm_num [ edgeWeightSumLight_eq_half, weightedDistLight_eq_half ]

/-! ## Prefix distance bound -/

/-
The VWSP light distance to any vertex on a walk is ≤ the walk prefix weight.
-/
omit [Fintype V] in
lemma walk_prefix_dist_le {G : SimpleGraph V} {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) (_hconn : G.Connected) {x a : V}
    (p : G.Walk x a) {u : V} (hu : u ∈ p.support) :
    G.weightedDistLight w x u ≤ (p.takeUntil u hu).edgeWeightSumLight w := by
  refine' csInf_le _ _;
  · exact ⟨ 0, Set.forall_mem_range.2 fun p => edgeWeightSumLight_nonneg hw p ⟩;
  · exact ⟨ _, rfl ⟩

/-! ## Optimal walk properties -/

/-
On an optimal walk from x to a, every intermediate vertex u satisfies
    dist(x,u) + dist(u,a) = dist(x,a) (geodesic property).
-/
omit [Fintype V] in
lemma optimal_walk_geodesic {G : SimpleGraph V} {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) (hconn : G.Connected) {x a : V}
    (p : G.Walk x a) (hp : p.edgeWeightSumLight w = G.weightedDistLight w x a)
    {u : V} (hu : u ∈ p.support) :
    G.weightedDistLight w x u + G.weightedDistLight w u a =
    G.weightedDistLight w x a := by
  -- Let F(s, t) be the set of all walks from s to t. By taking a walk in F(x, u) and appending a walk in F(u, a), we obtain a walk in F(x, a) which has light sum equal to the sum of the light sums of the two subwalks; thus inf F(x, a) ≤ inf F(x, u) + inf F(u, a). This is the triangle inequality.
  have h_triangle : G.weightedDistLight w x a ≤ G.weightedDistLight w x u + G.weightedDistLight w u a := by
    simp +decide only [weightedDistLight_eq_half];
    linarith [ weightedDist_triangle' hw hconn x u a ];
  -- By the properties of the edge weight sum, we have:
  have h_edge_weight_sum : p.edgeWeightSumLight w = (p.takeUntil u hu).edgeWeightSumLight w + (p.dropUntil u hu).edgeWeightSumLight w := by
    convert edgeWeightSumLight_eq_half w p using 1;
    convert edgeWeightSumLight_eq_half w ( p.takeUntil u hu |> Walk.append <| p.dropUntil u hu ) using 1;
    · rw [ edgeWeightSumLight_eq_half, edgeWeightSumLight_eq_half, edgeWeightSumLight_eq_half, edgeWeightSum_append' ];
      ring;
    · rw [ SimpleGraph.Walk.take_spec ];
  refine' le_antisymm _ _;
  · refine' add_le_of_le_sub_left _;
    refine' le_trans _ ( sub_le_sub_left ( walk_prefix_dist_le hw hconn p hu ) _ );
    exact ciInf_le ( show BddBelow ( Set.range fun p : G.Walk u a => p.edgeWeightSumLight w ) from ⟨ 0, Set.forall_mem_range.2 fun p => edgeWeightSumLight_nonneg hw p ⟩ ) ( p.dropUntil u hu ) |> le_trans <| by linarith;
  · exact h_triangle

omit [Fintype V] in
/-- On an optimal walk from x to a, every intermediate vertex u has
    dist(x,u) ≤ dist(x,a) in the light metric. -/
lemma optimal_walk_in_ball {G : SimpleGraph V} {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) (hconn : G.Connected) {x a : V}
    (p : G.Walk x a) (hp : p.edgeWeightSumLight w = G.weightedDistLight w x a)
    {u : V} (hu : u ∈ p.support) :
    G.weightedDistLight w x u ≤ G.weightedDistLight w x a := by
  have hgeo := optimal_walk_geodesic hw hconn p hp hu
  have : Nonempty (G.Walk u a) := hconn.preconnected u a
  linarith [show 0 ≤ G.weightedDistLight w u a from by
    rw [weightedDistLight_eq_half]; exact div_nonneg
      (le_ciInf fun q => edgeWeightSum_nonneg hw q) (by norm_num)]

/-! ## Walk support → graph set connected -/

/-
The support of a walk is graph-set-connected.
-/
omit [Fintype V] in
lemma walk_support_graphSetConnected {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) :
    graphSetConnected G (p.support.toFinset : Set V) := by
  constructor;
  · cases p <;> aesop;
  · intro x hx y hy;
    -- Since $x$ and $y$ are in the support of $p$, there exist indices $i$ and $j$ such that $x = p.getVert i$ and $y = p.getVert j$.
    obtain ⟨i, hi⟩ : ∃ i : Fin (p.length + 1), x = p.getVert i := by
      simp_all +decide [ List.mem_iff_get ];
      grind +suggestions
    obtain ⟨j, hj⟩ : ∃ j : Fin (p.length + 1), y = p.getVert j := by
      simp +zetaDelta at *;
      have h_support : ∀ {u v : V} {p : SimpleGraph.Walk G u v}, ∀ y ∈ p.support, ∃ j : Fin (p.length + 1), y = p.getVert j := 
by
        intros u v p y hy; induction' p with u v p ih <;> simp_all +decide [ SimpleGraph.Walk.getVert ] ;
        rcases hy with ( rfl | hy ) <;> [ exact ⟨ 0, rfl ⟩ ; exact Exists.elim ( ‹y ∈ _ → ∃ j : Fin ( _ + 1 ), y = _› hy ) fun j hj => ⟨ Fin.succ j, by simpa [ SimpleGraph.Walk.getVert ] using hj ⟩ ];
      exact h_support y hy;
    -- By definition of $p$, we know that $p.getVert i$ and $p.getVert j$ are connected by a path in $p$.
    have h_path : ∀ i j : Fin (p.length + 1), i ≤ j → Relation.ReflTransGen (fun a b => a ∈ p.support.toFinset ∧ b ∈ p.support.toFinset ∧ G.Adj a b) (p.getVert i) (p.getVert j) := by
      intro i j hij
      induction' j using Fin.induction with j ih;
      · aesop;
      · cases hij.eq_or_lt <;> simp_all +decide [ Fin.le_iff_val_le_val ];
        · rfl;
        · grind +suggestions;
    cases le_total i j <;> simp_all +decide;
    have h_symm : ∀ a b : V, G.Adj a b → G.Adj b a := by
      exact fun a b hab => hab.symm;
    have h_symm : ∀ a b : V, Relation.ReflTransGen (fun a b => a ∈ p.support ∧ b ∈ p.support ∧ G.Adj a b) a b → Relation.ReflTransGen (fun a b => a ∈ p.support ∧ b ∈ p.support ∧ G.Adj a b) b a := by
      intro a b hab; induction hab; aesop;
      exact .single ⟨ by tauto, by tauto, h_symm _ _ ( by tauto ) ⟩ |> Relation.ReflTransGen.trans <| by tauto;
    grind +qlia

/-! ## hG_ball and hG_path for VWSP metric -/

/-! ## Helper lemmas for hG_ball -/

/-
A walk from a ∈ A to y with weight ≤ r has all vertices in setBall A r.
-/
lemma walk_vertices_in_setBall {G : SimpleGraph V}
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (hconn : G.Connected)
    {a y : V} {A : Set V} (haA : a ∈ A) {r : ℝ}
    (p : G.Walk a y) (hp : p.edgeWeightSumLight w = G.weightedDistLight w a y)
    (hr : G.weightedDistLight w a y ≤ r) :
    ∀ u ∈ p.support,
      u ∈ @setBall V (vwspPMSLight G w hw hconn) A r := by
  intro u hu
  have h_dist : G.weightedDistLight w a u ≤ r := by
    exact le_trans ( optimal_walk_in_ball hw hconn p hp hu ) hr;
  exact ⟨ a, haA, h_dist ⟩

/-
For a, b ∈ A with dist(a,b) ≤ δ, optimal walk from a to b
    has all vertices in setBall A (δ/2).
-/
lemma chain_walk_vertices_in_setBall_half {G : SimpleGraph V}
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (hconn : G.Connected)
    {a b : V} {A : Set V} (haA : a ∈ A) (hbA : b ∈ A)
    {δ : ℝ} (hab : G.weightedDistLight w a b ≤ δ)
    (p : G.Walk a b) (hp : p.edgeWeightSumLight w = G.weightedDistLight w a b) :
    ∀ u ∈ p.support,
      u ∈ @setBall V (vwspPMSLight G w hw hconn) A (δ / 2) := by
  intro u hu
  have hgeodesic : G.weightedDistLight w a u + G.weightedDistLight w u b = G.weightedDistLight w a b := by
    exact optimal_walk_geodesic hw hconn p hp hu;
  -- By definition of `setBall`, we need to show that there exists some $x � \�in A$ such that $dist(x, u) \leq \delta / 2$.
  have h_dist_le : G.weightedDistLight w a u ≤ δ / 2 ∨ G.weightedDistLight w u b ≤ δ / 2 := by
    contrapose! hab; linarith;
  cases' h_dist_le with h h;
  · exact ⟨ a, haA, h ⟩;
  · use b, hbA;
    convert h using 1;
    exact vwspPMSLight G w hw hconn |>.dist_comm _ _

/-
If a walk's vertices are all in S, the endpoints are connected through S.
-/
omit [Fintype V] [DecidableEq V] in
lemma walk_connected_in_set {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) {S : Set V}
    (hsub : ∀ x ∈ p.support, x ∈ S) :
    Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ G.Adj a b) u v := by
  induction p <;> simp_all +decide [  ];
  · rfl;
  · grind +suggestions

/-
Two elements of A that are δ-chain-connected are graph-connected through
    setBall A (δ/2) in the VWSP light metric.
-/
lemma chain_connected_through_setBall {G : SimpleGraph V}
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (hconn : G.Connected)
    {A : Set V} {δ : ℝ} (_hδ : 0 ≤ δ)
    {a₁ a₂ : V} (_ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    (hchain : Relation.ReflTransGen
      (@chainRel V (vwspPMSLight G w hw hconn) A δ) a₁ a₂) :
    let S := @setBall V (vwspPMSLight G w hw hconn) A (δ / 2)
    Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ G.Adj x y) a₁ a₂ := by
  induction hchain;
  · exact .refl;
  · rename_i b c hb hc ih;
    -- By definition of `chain �Rel�`, we know that `b` and `c` are δ-chain-connected.
    obtain ⟨hbA, hcA, hbc⟩ := hc;
    -- By definition of `chainRel �`,� we know that there exists a walk from `b` to `c` with length at most `δ`.
    obtain ⟨p, hp⟩ : ∃ p : G.Walk b c, p.edgeWeightSumLight w = G.weightedDistLight w b c := by
      exact weightedDistLight_achieved hw hconn b c;
    -- By definition of `chainWalkVertices�InSetBallHalf`, all vertices on `p` are in `setBall A (δ / 2)`.
    have h_vertices_in_ball : ∀ u ∈ p.support, u ∈ @setBall V (vwspPMSLight G w hw hconn) A (δ / 2) := by
      apply chain_walk_vertices_in_setBall_half hw hconn hbA hcA hbc p hp;
    exact Relation.ReflTransGen.trans ( ih hbA ) ( walk_connected_in_set p h_vertices_in_ball )

/-
hG_ball for the VWSP light metric: δ-connected sets have graph-connected δ/2-balls.
-/
theorem vwsp_hG_ball {G : SimpleGraph V} [DecidableRel G.Adj]
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (hconn : G.Connected)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ (A : Set V),
      @deltaConnected V (vwspPMSLight G w hw hconn) δ A →
      graphSetConnected G (@setBall V (vwspPMSLight G w hw hconn) A (δ / 2)) := by
  -- Let's take any A that is delta-connected. We need to show that the setBall A (δ/2) is graphSetConnected.
  intro A hA
  apply And.intro;
  · cases' hA.1 with a ha;
    use a;
    exact ⟨ a, ha, by simp +decide ; linarith ⟩;
  · intro x hx y hy
    obtain ⟨a₁, ha₁A, ha₁x⟩ : ∃ a₁ ∈ A, G.weightedDistLight w a₁ x ≤ δ / 2 := by
      obtain ⟨ a₁, ha₁A, ha₁x ⟩ := hx;
      exact ⟨ a₁, ha₁A, by simpa [ vwspPMSLight ] using ha₁x ⟩
    obtain ⟨a₂, ha₂A, ha₂y⟩ : ∃ a₂ ∈ A, G.weightedDistLight w a₂ y ≤ δ / 2 := by
      exact inter_nonempty.mp hy;
    -- By the properties of the weighted distance, we have that $a₁$ and $a₂$ are connected through $A$.
    have h_chain : Relation.ReflTransGen (fun a b => a ∈ @setBall V (vwspPMSLight G w hw hconn) A (δ / 2) ∧ b ∈ @setBall V (vwspPMSLight G w hw hconn) A (δ / 2) ∧ G.Adj a b) a₁ a₂ := by
      apply chain_connected_through_setBall hw hconn hδ ha₁A ha₂A (hA.2 a₁ ha₁A a₂ ha₂A);
    -- By the properties of the weighted distance, we have that $x$ and $a₁$ are connected through $A$.
    have h_chain_x_a₁ : Relation.ReflTransGen (fun a b => a ∈ @setBall V (vwspPMSLight G w hw hconn) A (δ / 2) ∧ b ∈ @setBall V (vwspPMSLight G w hw hconn) A (δ / 2) ∧ G.Adj a b) x a₁ := by
      have h_chain_x_a₁ : ∀ u ∈ (weightedDistLight_achieved hw hconn a₁ x).choose.support, u ∈ @setBall V (vwspPMSLight G w hw hconn) A (δ / 2) := by
        apply walk_vertices_in_setBall hw hconn ha₁A (weightedDistLight_achieved hw hconn a₁ x).choose (weightedDistLight_achieved hw hconn a₁ x).choose_spec ha₁x;
      have h_chain_x_a₁ : Relation.ReflTransGen (fun a b => a ∈ @setBall V (vwspPMSLight G w hw hconn) A (δ / 2) ∧ b ∈ @setBall V (vwspPMSLight G w hw hconn) A (δ / 2) ∧ G.Adj a b) a₁ x := by
        exact walk_connected_in_set (weightedDistLight_achieved hw hconn a₁ x).choose h_chain_x_a₁;
      have h_chain_x_a₁_symm : ∀ {a b : V}, Relation.ReflTransGen (fun a b => a ∈ @setBall V (vwspPMSLight G w hw hconn) A (δ / 2) ∧ b ∈ @setBall V (vwspPMSLight G w hw hconn) A (δ / 2) ∧ G.Adj a b) a b → Relation.ReflTransGen (fun a b => a ∈ @setBall V (vwspPMSLight G w hw hconn) A (δ / 2) ∧ b ∈ @setBall V (vwspPMSLight G w hw hconn) A (δ / 2) ∧ G.Adj a b) b a := by
        intro a b hab
        induction' hab with a b hab ih;
        · rfl;
        · exact .single ⟨ ih.2.1, ih.1, ih.2.2.symm ⟩ |> Relation.ReflTransGen.trans <| by assumption;
      exact h_chain_x_a₁_symm h_chain_x_a₁;
    -- By the properties of the weighted distance, we have that $a₂$ and $y$ are connected through $A$.
    have h_chain_a₂_y : Relation.ReflTransGen (fun a b => a ∈ @setBall V (vwspPMSLight G w hw hconn) A (δ / 2) ∧ b ∈ @setBall V (vwspPMSLight G w hw hconn) A (δ / 2) ∧ G.Adj a b) a₂ y := by
      obtain ⟨ p, hp ⟩ := weightedDistLight_achieved hw hconn a₂ y;
      apply walk_connected_in_set p (fun u hu => by
        apply walk_vertices_in_setBall hw hconn ha₂A p hp (by linarith) u hu);
    exact h_chain_x_a₁.trans ( h_chain.trans h_chain_a₂_y )

/-
hG_path for the VWSP light metric: shortest path existence with geodesic property.
-/
theorem vwsp_hG_path {G : SimpleGraph V} [DecidableRel G.Adj]
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (hconn : G.Connected)
    {δ : ℝ} (_hδ : 0 ≤ δ) :
    ∀ (x : V) (A : Set V) (r : ℝ), A.Nonempty →
      r ≤ 5 * δ →
      (∃ a ∈ A, @dist V (vwspPMSLight G w hw hconn).toDist x a ≤ r) →
      ∃ (P : Set V) (a : V), a ∈ A ∩ P ∧ x ∈ P ∧
        graphSetConnected G P ∧
        P ⊆ @setBall V (vwspPMSLight G w hw hconn) {x} r ∧
        ∀ u ∈ P, @dist V (vwspPMSLight G w hw hconn).toDist x u +
          @dist V (vwspPMSLight G w hw hconn).toDist u a =
          @dist V (vwspPMSLight G w hw hconn).toDist x a := by
  intro x A r hA _hr h_exists
  obtain ⟨a₀, ha₀A, ha₀⟩ := h_exists
  obtain ⟨p, hp⟩ := weightedDistLight_achieved hw hconn x a₀
  use p.support.toFinset, a₀;
  refine' ⟨ ⟨ ha₀A, _ ⟩, _, _, _, _ ⟩;
  · aesop;
  · simp +decide;
  · exact walk_support_graphSetConnected p;
  · intro u hu;
    refine' ⟨ x, _, _ ⟩ <;> simp_all +decide;
    refine' le_trans _ ha₀;
    convert optimal_walk_in_ball hw hconn p hp hu using 1;
  · intro u hu;
    convert optimal_walk_geodesic hw hconn p hp ( by simpa using hu ) using 1

end
