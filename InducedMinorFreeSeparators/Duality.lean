/-
# LP Strong Duality: Q(G) = QDual(G)

Proved using Farkas' lemma (geometric Hahn-Banach separation for cones)
from `Mathlib.Analysis.Convex.Cone.Dual`.
-/
import Mathlib
import InducedMinorFreeSeparators.ProofDefs

open Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Qspread properties -/

/-
The Qspread set is bounded above for connected graphs.
-/
lemma Qspread_bddAbove' (G : SimpleGraph V) (hconn : G.Connected) :
    BddAbove { val | ∃ w : V → ℝ, (∀ v, 0 ≤ w v) ∧ (∑ v, w v ≤ 1) ∧
      val = ∑ u : V, ∑ v : V, G.weightedDist w u v } := by
  use (Fintype.card V)^2 * 2 * Fintype.card V;
  rintro x ⟨ w, hw₁, hw₂, rfl ⟩;
  -- For connected G and feasible w, d_w(u,v) ≤ 2n via a path of length ≤ n.
  have h_path_length : ∀ u v : V, G.weightedDist w u v ≤ 2 * Fintype.card V := by
    intro u v
    obtain ⟨P, hP⟩ : ∃ P : G.Walk u v, P.length ≤ Fintype.card V := by
      -- Since $G$ is connected, there exists � a� path from $u$ to $v$.
      obtain ⟨P, hP⟩ : ∃ P : G.Walk u v, P.IsPath := by
        have := hconn u v;
        obtain ⟨ P, hP ⟩ := this.exists_isPath; exact ⟨ P, hP ⟩ ;
      exact ⟨ P, by simpa using hP.length_lt.le ⟩
    have hP_weight : P.edgeWeightSum w ≤ 2 * Fintype.card V := by
      have hP_weight : ∀ u v : V, ∀ P : G.Walk u v, P.edgeWeightSum w ≤ 2 * P.length := by
        intro u v P
        induction' P with u v P ih;
        · simp +decide [ SimpleGraph.Walk.edgeWeightSum ];
        · simp_all +decide [ SimpleGraph.Walk.edgeWeightSum ];
          linarith [ hw₁ v, hw₁ P, show w v ≤ 1 from le_trans ( Finset.single_le_sum ( fun a _ => hw₁ a ) ( Finset.mem_univ v ) ) hw₂, show w P ≤ 1 from le_trans ( Finset.single_le_sum ( fun a _ => hw₁ a ) ( Finset.mem_univ P ) ) hw₂ ];
      exact le_trans ( hP_weight u v P ) ( mul_le_mul_of_nonneg_left ( mod_cast hP ) zero_le_two )
    have hP_dist : G.weightedDist w u v ≤ P.edgeWeightSum w := by
      exact ciInf_le ( show BddBelow ( Set.range ( fun p : G.Walk u v => p.edgeWeightSum w ) ) from ⟨ 0, Set.forall_mem_range.2 fun p => by
                        induction p <;> simp +decide [ *, SimpleGraph.Walk.edgeWeightSum ];
                        rename_i u v w huv p ih;
                        exact add_nonneg ( add_nonneg ( hw₁ u ) ( hw₁ v ) ) ( by exact ( show 0 ≤ SimpleGraph.Walk.edgeWeightSum _ p from by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact by rw [ edgeWeightSum_eq_sum_vertexLoad ] ; exact Finset.sum_nonneg fun _ _ => mul_nonneg ( hw₁ _ ) ( Nat.cast_nonneg _ ) ) ) ) ) ) ) ) ) ⟩ ) P |> le_trans <| by simp +decide ;
    linarith [hP_weight, hP_dist];
  refine' le_trans ( Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => h_path_length u v ) _ ; norm_num ; ring_nf ; norm_num

/-- Any feasible weight gives a value ≤ Qspread. -/
lemma Qspread_ge_of_feasible (G : SimpleGraph V) (hconn : G.Connected)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hw1 : ∑ v, w v ≤ 1) :
    ∑ u : V, ∑ v : V, G.weightedDist w u v ≤ Qspread G :=
  le_csSup (Qspread_bddAbove' G hconn) ⟨w, hw, hw1, rfl⟩

/-
Qspread is nonneg for connected graphs.
-/
lemma Qspread_nonneg' (G : SimpleGraph V) (hconn : G.Connected) :
    0 ≤ Qspread G := by
  apply le_csSup;
  · exact Qspread_bddAbove' G hconn;
  · refine' ⟨ fun _ => 0, _, _, _ ⟩ <;> norm_num;
    refine' Eq.symm ( Finset.sum_eq_zero fun u hu => Finset.sum_eq_zero fun v hv => _ );
    convert weightedDist_smul 0 ( by norm_num ) ( fun _ => 1 ) u v ; norm_num;
    ring

/-! ## Weak Duality -/

/-
For any feasible w and valid routing R, the spread ≤ max congestion.
-/
lemma spread_le_routing_congestion (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hw1 : ∑ v, w v ≤ 1)
    (R : (u v : V) → G.Path u v → ℝ)
    (hR_nn : ∀ u v P, 0 ≤ R u v P)
    (hR_sum : ∀ u v, ∑ P : G.Path u v, R u v P = 1) :
    ∑ u : V, ∑ v : V, G.weightedDist w u v ≤
      Finset.univ.sup' Finset.univ_nonempty (fun x => routingCongestion R x) := by
  -- For each pair (u,v), d_w(u,v) ≤_P � R�(u,v,P) · cost(P,w) since d_w ≤ � cost�(P) for each P and R is a probability distribution over paths.
  have h_le : ∀ u v, G.weightedDist w u v ≤ ∑ P : G.Path u v, R u v P * ∑ x : V, w x * (P : G.Walk u v).vertexLoad x := by
    intro u v
    have h_le : ∀ P : G.Path u v, G.weightedDist w u v ≤ P.val.edgeWeightSum w := by
      intro P;
      exact ciInf_le ⟨ 0, Set.forall_mem_range.2 fun p => by
        induction p <;> simp +decide [ *, SimpleGraph.Walk.edgeWeightSum ];
        rename_i u v w huv p ih;
        exact add_nonneg ( add_nonneg ( hw u ) ( hw v ) ) ( ih ( p.toPath ) ) ⟩ _
    have h_le_sum : G.weightedDist w u v ≤ ∑ P : G.Path u v, R u v P * P.val.edgeWeightSum w := by
      refine' le_trans _ ( Finset.sum_le_sum fun P _ => mul_le_mul_of_nonneg_left ( h_le P ) ( hR_nn u v P ) );
      rw [ ← Finset.sum_mul _ _ _, hR_sum, one_mul ]
    exact (by
    convert h_le_sum using 3 ; rw [ edgeWeightSum_eq_sum_vertexLoad ]);
  refine' le_trans ( Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => h_le u v ) _;
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ u, ∑ v, ∑ P : G.Path u v, R u v P * ∑ x : V, w x * (P : G.Walk u v).vertexLoad x = ∑ x : V, w x * ∑ u, ∑ v, ∑ P : G.Path u v, R u v P * (P : G.Walk u v).vertexLoad x := by
    simp +decide only [← sum_product'];
    simp +decide only [sum_sigma'];
    simp +decide only [Finset.mul_sum _ _ _];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
  rw [ h_fubini ];
  refine' le_trans ( Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left _ ( hw x ) ) _;
  rotate_left;
  use fun x => Finset.univ.sup' Finset.univ_nonempty ( fun x => routingCongestion R x );
  · rw [ ← Finset.sum_mul _ _ _ ] ; exact mul_le_of_le_one_left ( by exact le_trans ( by norm_num ) ( Finset.le_sup' ( fun x => routingCongestion R x ) ( Finset.mem_univ ( Classical.arbitrary V ) ) |> le_trans ( show 0 ≤ routingCongestion R ( Classical.arbitrary V ) from Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg ( hR_nn _ _ _ ) ( Nat.cast_nonneg _ ) ) ) ) hw1;
  · exact Finset.le_sup' ( fun x => routingCongestion R x ) ( Finset.mem_univ x )

/-
Weak duality: Qspread ≤ QDual.
-/
theorem weak_duality (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hconn : G.Connected) : Qspread G ≤ QDual G := by
  -- For any feasible w, the spread is less than or equal to the infimum of the congestion.
  have h_le_inf : ∀ w : V → ℝ, (∀ v, 0 ≤ w v) → (∑ v, w v ≤ 1) → ∑ u : V, ∑ v : V, G.weightedDist w u v ≤ QDual G := by
    intro w hw hw1
    obtain ⟨R, hR_nn, hR_sum⟩ : ∃ R : (u v : V) → G.Path u v → ℝ, (∀ u v P, 0 ≤ R u v P) ∧ (∀ u v, ∑ P : G.Path u v, R u v P = 1) := by
      -- Since G is connected, for any u and � v�, there exists at least one path from u to v.
      have h_path_exists : ∀ u v : V, ∃ P : G.Path u v, True := by
        intro u v; have := hconn u v; simp_all +decide [ SimpleGraph.Reachable ] ;
        exact SimpleGraph.Reachable.exists_isPath this;
      choose P hP using h_path_exists;
      refine' ⟨ fun u v P' => if P' = P u v then 1 else 0, _, _ ⟩ <;> aesop;
    exact le_csInf ⟨ _, ⟨ R, hR_nn, hR_sum, rfl ⟩ ⟩ fun μ ⟨ R', hR'_nn, hR'_sum, hμ ⟩ => by simpa [ hμ ] using spread_le_routing_congestion G w hw hw1 R' hR'_nn hR'_sum;
  exact csSup_le ⟨ _, ⟨ 0, fun _ => by norm_num, by norm_num, rfl ⟩ ⟩ ( by rintro x ⟨ w, hw, hw1, rfl ⟩ ; exact h_le_inf w hw hw1 )

/-! ## Strong Duality -/

/-- The set of integral routing congestion vectors. -/
noncomputable def integralCongestionSet (G : SimpleGraph V) [DecidableRel G.Adj] :
    Set (V → ℝ) :=
  Set.range (fun (R : (u : V) → (v : V) → G.Path u v) =>
    (fun x : V => (∑ u : V, ∑ v : V,
      ((R u v : G.Walk u v).vertexLoad x : ℝ))))

/-- The integral congestion set is finite. -/
lemma integralCongestionSet_finite (G : SimpleGraph V) [DecidableRel G.Adj] :
    (integralCongestionSet G).Finite :=
  Set.finite_range _

/-
For an integral routing, QDual ≤ max congestion.
-/
lemma QDual_le_integral_congestion
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (R : (u : V) → (v : V) → G.Path u v) :
    QDual G ≤ Finset.univ.sup' Finset.univ_nonempty
      (fun x => (∑ u : V, ∑ v : V, ((R u v : G.Walk u v).vertexLoad x : ℝ))) := by
  refine' csInf_le _ _;
  · exact ⟨ 0, by rintro x ⟨ R, hR₁, hR₂, rfl ⟩ ; exact Finset.le_sup' ( fun x => routingCongestion R x ) ( Finset.mem_univ ( Classical.arbitrary V ) ) |> le_trans ( by exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg ( hR₁ _ _ _ ) ( Nat.cast_nonneg _ ) ) ⟩;
  · use fun u v P => if P = R u v then 1 else 0;
    unfold routingCongestion; aesop;

/-
Every element of the convex hull of integral congestion vectors has
max ≥ QDual (since it corresponds to a fractional routing).
-/
lemma convexHull_congestion_max_ge_QDual
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (_hconn : G.Connected) :
    ∀ c ∈ convexHull ℝ (integralCongestionSet G),
      QDual G ≤ Finset.univ.sup' Finset.univ_nonempty (fun x => c x) := by
  -- Let $S$ be the set of congestion vectors of valid fractional routings.
  set S : Set (V → ℝ) := {c | ∃ R : (u v : V) → G.Path u v → ℝ, (∀ u v P, 0 ≤ R u v P) ∧ (∀ u v, ∑ P : G.Path u v, R u v P = 1) ∧ c = fun x => routingCongestion R x};
  -- To show that every element in the convex hull of the integral congestion set has a maximum congestion that's at least QDual, we need to show that the integral congestion set is a subset of S and that S � is� convex.
  have h_subset : integralCongestionSet G ⊆ S := by
    rintro _ ⟨ R, rfl ⟩;
    refine' ⟨ fun u v P => if P = R u v then 1 else 0, _, _, _ ⟩ <;> simp +decide [ routingCongestion ];
    exact fun _ _ _ _ => by split_ifs <;> norm_num;
  have h_convex : Convex ℝ S := by
    rintro c₁ ⟨ R₁, hR₁₁, hR₁₂, rfl ⟩ c₂ ⟨ R₂, hR₂₁, hR₂₂, rfl ⟩ a b ha hb hab;
    refine' ⟨ fun u v P => a * R₁ u v P + b * R₂ u v P, _, _, _ ⟩ <;> simp_all +decide [ Finset.sum_add_distrib ];
    · exact fun u v P hP => add_nonneg ( mul_nonneg ha ( hR₁₁ u v P hP ) ) ( mul_nonneg hb ( hR₂₁ u v P hP ) );
    · simp +decide [ ← Finset.mul_sum, hR₁₂, hR₂₂, hab ];
    · ext x; simp +decide [ routingCongestion, Finset.sum_add_distrib, add_mul, Finset.mul_sum ] ; ring_nf;
  intro c hc;
  rw [ mem_convexHull_iff ] at hc;
  obtain ⟨ R, hR₁, hR₂, rfl ⟩ := hc S h_subset h_convex;
  exact csInf_le ⟨ 0, by rintro x ⟨ R, hR₁, hR₂, rfl ⟩ ; exact Finset.le_sup' ( fun x => routingCongestion R x ) ( Finset.mem_univ ( Classical.choose ( Finset.card_pos.mp ( Fintype.card_pos ) ) ) ) |> le_trans ( by exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg ( hR₁ _ _ _ ) ( Nat.cast_nonneg _ ) ) ⟩ ⟨ R, hR₁, hR₂, rfl ⟩

omit [Fintype V] [DecidableEq V] in
omit [Fintype V] [DecidableEq V] in
omit [Fintype V] [DecidableEq V] in
/-- B = { c : ∀ x, c x ≤ α } is closed. -/
lemma isClosed_le_const (α : ℝ) :
    IsClosed { c : V → ℝ | ∀ x, c x ≤ α } := by
  simpa only [Set.setOf_forall] using
    isClosed_iInter fun x => isClosed_Iic.preimage (continuous_apply x)

/-
B = { c : ∀ x, c x ≤ α } is convex.
-/
omit [Fintype V] [DecidableEq V] in
lemma convex_le_const (α : ℝ) :
    Convex ℝ { c : V → ℝ | ∀ x, c x ≤ α } := by
  intro c hc d hd a b ha hb hab;
  exact fun x => by rw [ ← eq_sub_iff_add_eq' ] at hab; simpa [ hab ] using by nlinarith [ hc x, hd x ] ;

/-
If f is a CLF on V → ℝ with f bounded above on {c | max c ≤ α}, then
the representing weights are nonneg.
-/
lemma clf_nonneg_of_bounded_on_B
    (f : (V → ℝ) →L[ℝ] ℝ) (α u_val : ℝ)
    (hfB : ∀ a ∈ { c : V → ℝ | ∀ x, c x ≤ α }, f a < u_val)
    (hf_eq : ∀ c : V → ℝ, f c = ∑ x : V, f (Pi.single x (1 : ℝ)) * c x)
    (x₀ : V) : 0 ≤ f (Pi.single x₀ (1 : ℝ)) := by
  -- For large n : ℕ, define c_n : V → ℝ by c_n(x) = if x = x₀ then α - n else α.
  by_contra h_neg
  obtain ⟨n, hn⟩ : ∃ n : ℕ, f (fun x => if x = x₀ then α - n else α) > u_val := by
    have h_archimedean : Filter.Tendsto (fun n : ℕ => f (fun x => if x = x₀ then α - n else α)) Filter.atTop Filter.atTop := by
      -- By definition of $f$, we can expand $f(c_n)$.
      have h_expand : ∀ n : ℕ, f (fun x => if x = x₀ then α - n else α) = f (fun x => α) - n * f (Pi.single x₀ 1) := by
        intro n
        rw [hf_eq, hf_eq];
        simp +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ] ; ring;
      exact Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Nat.ceil ( ( x - f ( fun _ => α ) ) / ( -f ( Pi.single x₀ 1 ) ) ), fun n hn => by nlinarith [ Nat.ceil_le.mp hn, h_expand n, mul_div_cancel₀ ( x - f ( fun _ => α ) ) ( by linarith : ( -f ( Pi.single x₀ 1 ) ) ≠ 0 ) ] ⟩;
    exact ( h_archimedean.eventually_gt_atTop u_val ) |> fun h => h.exists;
  exact hn.not_ge ( le_of_lt ( hfB _ fun x => by by_cases hx : x = x₀ <;> simp +decide [ hx ] ) )

/-- If w ≥ 0, f = Σ w·c, f < u on B, f > v on A (≠ ∅), u < v, then Σ w > 0. -/
lemma sum_pos_of_separation
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hconn : G.Connected)
    (f : (V → ℝ) →L[ℝ] ℝ) (u_val v_val : ℝ)
    (w : V → ℝ) (hw_nn : ∀ x, 0 ≤ w x)
    (hf_eq : ∀ c : V → ℝ, f c = ∑ x : V, w x * c x)
    (hfB : ∀ a ∈ { c : V → ℝ | ∀ x, c x ≤ Qspread G }, f a < u_val)
    (hfA : ∀ b ∈ convexHull ℝ (integralCongestionSet G), v_val < f b)
    (huv : u_val < v_val) :
    0 < ∑ x : V, w x := by
  by_contra h_le; push_neg at h_le
  have hw_zero : ∀ x, w x = 0 :=
    fun x => le_antisymm (le_trans (Finset.single_le_sum (fun a _ => hw_nn a)
      (Finset.mem_univ x)) h_le) (hw_nn x)
  have hf_zero : ∀ c : V → ℝ, f c = 0 := by
    intro c; rw [hf_eq]; exact Finset.sum_eq_zero fun x _ => by simp [hw_zero x]
  -- f ≡ 0 contradicts hfB and hfA: hfB gives 0 < u_val, hfA gives v_val < 0
  have h1 : 0 < u_val := by
    have : (0 : V → ℝ) ∈ { c : V → ℝ | ∀ x, c x ≤ Qspread G } :=
      fun x => Qspread_nonneg' G hconn
    linarith [hfB 0 this, hf_zero 0]
  have hA_ne : (convexHull ℝ (integralCongestionSet G)).Nonempty := by
    rw [convexHull_nonempty_iff]
    have : ∀ u v : V, Nonempty (G.Path u v) := fun u v =>
      ⟨(hconn u v).some.toPath⟩
    exact ⟨_, Set.mem_range.mpr ⟨fun u v => Classical.arbitrary _, rfl⟩⟩
  obtain ⟨a, ha⟩ := hA_ne
  linarith [hfA a ha, hf_zero a]

omit [Fintype V] [DecidableEq V] in
private lemma edgeWeightSum_append' {G : SimpleGraph V}
    (w : V → ℝ) {u v t : V} (p : G.Walk u v) (q : G.Walk v t) :
    (p.append q).edgeWeightSum w = p.edgeWeightSum w + q.edgeWeightSum w := by
  induction p with
  | nil => simp [SimpleGraph.Walk.edgeWeightSum]
  | cons h rest ih => simp [SimpleGraph.Walk.edgeWeightSum, ih]; ring

omit [Fintype V] [DecidableEq V] in
private lemma edgeWeightSum_nonneg [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) {u v : V} (P : G.Walk u v) :
    0 ≤ P.edgeWeightSum w := by
  rw [edgeWeightSum_eq_sum_vertexLoad]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (Nat.cast_nonneg _)

private lemma edgeWeightSum_dropUntil_le {G : SimpleGraph V}
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) {u v : V} (P : G.Walk u v)
    (x : V) (hx : x ∈ P.support) :
    (P.dropUntil x hx).edgeWeightSum w ≤ P.edgeWeightSum w := by
  have hsplit := P.take_spec hx
  have : P.edgeWeightSum w = (P.takeUntil x hx).edgeWeightSum w +
      (P.dropUntil x hx).edgeWeightSum w := by
    conv_lhs => rw [← hsplit]; rw [edgeWeightSum_append']
  linarith [edgeWeightSum_nonneg w hw (P.takeUntil x hx)]

/-- For nonneg weights, Walk.bypass doesn't increase edgeWeightSum. -/
lemma edgeWeightSum_bypass_le {G : SimpleGraph V} [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) {u v : V} (P : G.Walk u v) :
    P.bypass.edgeWeightSum w ≤ P.edgeWeightSum w := by
  induction P with
  | nil => simp [SimpleGraph.Walk.bypass, SimpleGraph.Walk.edgeWeightSum]
  | cons hadj rest ih =>
    simp only [SimpleGraph.Walk.bypass]
    split
    · -- u ∈ rest.bypass.support: bypass drops to dropUntil
      rename_i hs
      calc (rest.bypass.dropUntil _ hs).edgeWeightSum w
          ≤ rest.bypass.edgeWeightSum w := edgeWeightSum_dropUntil_le w hw _ _ hs
        _ ≤ rest.edgeWeightSum w := ih
        _ ≤ _ + rest.edgeWeightSum w := le_add_of_nonneg_left (add_nonneg (hw _) (hw _))
    · -- u ∉ rest.bypass.support: bypass = cons hadj rest.bypass
      simp only [SimpleGraph.Walk.edgeWeightSum]
      linarith

/-- The spread under w exceeds Qspread * Σ w, given the separation. -/
lemma spread_gt_of_separation
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hconn : G.Connected)
    (f : (V → ℝ) →L[ℝ] ℝ) (u_val v_val : ℝ)
    (w : V → ℝ) (hw_nn : ∀ x, 0 ≤ w x)
    (hf_eq : ∀ c : V → ℝ, f c = ∑ x : V, w x * c x)
    (hfB : ∀ a ∈ { c : V → ℝ | ∀ x, c x ≤ Qspread G }, f a < u_val)
    (hfA : ∀ b ∈ convexHull ℝ (integralCongestionSet G), v_val < f b)
    (huv : u_val < v_val) :
    ∑ u : V, ∑ v : V, G.weightedDist w u v > Qspread G * ∑ x : V, w x := by
  -- Step 1: f(Qspread · 1) < u_val
  have hfQ : Qspread G * ∑ x : V, w x < u_val := by
    have : (fun (_ : V) => Qspread G) ∈ { c : V → ℝ | ∀ x, c x ≤ Qspread G } := fun _ => le_refl _
    have hlt := hfB _ this; rw [hf_eq] at hlt
    have : ∑ x : V, w x * Qspread G = Qspread G * ∑ x : V, w x := by
      rw [← Finset.sum_mul]; ring
    linarith
  -- Step 2: Pick shortest-path routing (minimizing cost for each pair)
  have hpath : ∀ u v : V, Nonempty (G.Path u v) := fun u v =>
    ⟨(hconn u v).some.toPath⟩
  -- For each (u,v), pick the path minimizing edgeWeightSum
  have hmin : ∀ u v : V, ∃ P : G.Path u v,
      ∀ Q : G.Path u v, (P : G.Walk u v).edgeWeightSum w ≤
        (Q : G.Walk u v).edgeWeightSum w := by
    intro u v
    exact Finset.exists_min_image Finset.univ
      (fun P : G.Path u v => (P : G.Walk u v).edgeWeightSum w)
      ⟨Classical.arbitrary _, Finset.mem_univ _⟩ |>.imp fun P hP =>
        fun Q => (hP.2 Q (Finset.mem_univ _))
  choose R hR using hmin
  -- R is in A
  have hR_in_A : (fun x : V => ∑ u : V, ∑ v : V,
      ((R u v : G.Walk u v).vertexLoad x : ℝ)) ∈
      convexHull ℝ (integralCongestionSet G) :=
    subset_convexHull ℝ _ ⟨R, rfl⟩
  have hfR := hfA _ hR_in_A
  -- f(cong_R) = Σ_{u,v} cost(R(u,v), w)
  have hf_cong : f (fun x => ∑ u : V, ∑ v : V,
      ((R u v : G.Walk u v).vertexLoad x : ℝ)) =
      ∑ u : V, ∑ v : V, (R u v : G.Walk u v).edgeWeightSum w := by
    rw [hf_eq]
    simp_rw [edgeWeightSum_eq_sum_vertexLoad]
    simp only [Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    congr 1; ext u; rw [Finset.sum_comm]
  -- d_w(u,v) = cost(R(u,v), w) since R picks shortest path among paths
  -- And d_w ≤ cost of any walk ≤ cost of shortest path
  have hcost_eq : ∀ u v : V, G.weightedDist w u v ≤
      (R u v : G.Walk u v).edgeWeightSum w := by
    intro u v
    exact ciInf_le ⟨0, Set.forall_mem_range.2 fun p => by
      rw [edgeWeightSum_eq_sum_vertexLoad]
      exact Finset.sum_nonneg fun x _ => mul_nonneg (hw_nn x) (Nat.cast_nonneg _)⟩
      (R u v).val
  have h1 : ∑ u, ∑ v, G.weightedDist w u v ≤
      ∑ u, ∑ v, (R u v : G.Walk u v).edgeWeightSum w :=
    Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hcost_eq u v
  -- Also, ∑ cost(R) = f(cong_R) > v_val > u_val > Qspread · Σ w
  -- We need: d_w(u,v) ≥ cost(shortest path) for each pair, giving = for shortest path
  -- Actually we have: Qspread · Σ w < u_val < v_val < f(cong_R) = Σ cost(R)
  -- And Σ d_w ≤ Σ cost(R). But also Σ d_w ≥ ? We need to reverse.
  -- The correct direction: Σ cost(R) is the MINIMUM over integral routings.
  -- For any path Q from u to v: cost(R(u,v)) ≤ cost(Q).
  -- And d_w(u,v) = inf over walks ≤ cost(Q) for any Q.
  -- But d_w ≤ cost(R) (≤ cost of any other path).
  -- However, d_w might equal cost(R) if inf = min over paths.
  -- For this we need: walk → path shortening. 
  -- Actually, d_w = iInf over walks. For w ≥ 0, walks that pass through
  -- a vertex multiple times can be shortened (removing loops decreases cost).
  -- So d_w = min over paths = cost(R(u,v)).
  -- Hence Σ d_w = Σ cost(R(u,v)) = f(cong_R) > Qspread · Σ w.
  -- For now, let's use: Σ cost(R) ≤ Σ d_w + slack, where slack ≥ 0.
  -- Actually no, Σ d_w ≤ Σ cost(R).
  -- We need Σ d_w > Qspread · Σ w. 
  -- Observation: for ANY integral routing, f(cong) > v > u > Qspread · Σ w.
  -- So Σ cost(any R) > Qspread · Σ w.
  -- Since R is the MIN-cost routing: Σ cost(R) ≤ Σ cost(any R').
  -- And d_w(u,v) ≤ cost(R(u,v)) for each pair.
  -- But d_w could be strictly less if there's a walk cheaper than any path.
  -- For w ≥ 0, d_w = min over paths = cost(R(u,v)). Let me just assert equality.
  have hcost_exact : ∀ u v : V, G.weightedDist w u v =
      (R u v : G.Walk u v).edgeWeightSum w := by
    intro u v
    exact le_antisymm (hcost_eq u v) (by
      haveI : Nonempty (G.Walk u v) := ⟨(hconn u v).some⟩
      exact le_ciInf (fun Q =>
        le_trans (hR u v Q.toPath) (edgeWeightSum_bypass_le w hw_nn Q)))
  have h_eq : ∑ u, ∑ v, G.weightedDist w u v =
      ∑ u, ∑ v, (R u v : G.Walk u v).edgeWeightSum w := by
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => hcost_exact u v
  linarith [hf_cong, hfR, huv, hfQ]

/-- Strong duality: QDual ≤ Qspread.
Uses Farkas' lemma (geometric Hahn-Banach separation theorem). -/
theorem strong_duality (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hconn : G.Connected) : QDual G ≤ Qspread G := by
  by_contra h_contra; push_neg at h_contra
  -- Sets for separation
  set A := convexHull ℝ (integralCongestionSet G) with hA_def
  set B := { c : V → ℝ | ∀ x, c x ≤ Qspread G } with hB_def
  -- Separation hypothesis check
  have hAB_disj : Disjoint B A := by
    rw [Set.disjoint_iff]; intro c ⟨hcB, hcA⟩
    have h1 := convexHull_congestion_max_ge_QDual G hconn c hcA
    have h2 : Finset.univ.sup' Finset.univ_nonempty (fun x => c x) ≤ Qspread G := by
      exact Finset.sup'_le _ _ fun x _ => hcB x
    linarith
  -- Apply geometric Hahn-Banach separation (Farkas' lemma)
  obtain ⟨f, u_val, v_val, hfB, huv, hfA⟩ :=
    geometric_hahn_banach_closed_compact (convex_le_const _) (isClosed_le_const _)
      (convex_convexHull ℝ _) ((integralCongestionSet_finite G).isCompact_convexHull) hAB_disj
  -- f(c) = Σ w(x) c(x) for w(x) = f(Pi.single x 1)
  set w : V → ℝ := fun x => f (Pi.single x (1 : ℝ)) with hw_def
  have hf_eq : ∀ c : V → ℝ, f c = ∑ x : V, w x * c x := by
    intro c
    conv_lhs => rw [show c = ∑ x : V, c x • (Pi.single x (1 : ℝ) : V → ℝ) from by
      ext y; simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]]
    simp only [map_sum, map_smul, smul_eq_mul]
    congr 1; ext x; ring
  -- w ≥ 0 (from B being unbounded below)
  have hw_nn : ∀ x₀ : V, 0 ≤ w x₀ :=
    fun x₀ => clf_nonneg_of_bounded_on_B f (Qspread G) u_val hfB hf_eq x₀
  -- Σ w > 0
  have hw_pos : 0 < ∑ x : V, w x :=
    sum_pos_of_separation G hconn f u_val v_val w hw_nn hf_eq hfB hfA huv
  -- Σ d_w > Qspread · Σ w
  have hspread_gt : ∑ u : V, ∑ v : V, G.weightedDist w u v >
      Qspread G * ∑ x : V, w x :=
    spread_gt_of_separation G hconn f u_val v_val w hw_nn hf_eq hfB hfA huv
  -- Contradiction via positive homogeneity
  set s := ∑ x : V, w x with hs_def
  have hs_pos : 0 < s := hw_pos
  have h_feasible_nn : ∀ v, 0 ≤ w v / s := fun v => div_nonneg (hw_nn v) (le_of_lt hs_pos)
  have h_feasible_sum : ∑ v, w v / s ≤ 1 := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]; exact le_of_eq (mul_inv_cancel₀ (ne_of_gt hs_pos))
  have h_homog : ∀ u' v', G.weightedDist w u' v' =
      s * G.weightedDist (fun x => w x / s) u' v' := by
    intro u' v'
    conv_lhs => rw [show w = fun x => s * (w x / s) from by ext x; field_simp]
    exact weightedDist_smul s (le_of_lt hs_pos) _ u' v'
  simp_rw [h_homog] at hspread_gt
  have hsd : s * ∑ u : V, ∑ v : V, G.weightedDist (fun x => w x / s) u v >
      Qspread G * s := by
    calc s * ∑ u, ∑ v, G.weightedDist (fun x => w x / s) u v
        = ∑ u, ∑ v, s * G.weightedDist (fun x => w x / s) u v := by
          rw [Finset.mul_sum]; congr 1; ext u; rw [Finset.mul_sum]
      _ > Qspread G * s := hspread_gt
  have hsd' : Qspread G < ∑ u : V, ∑ v : V, G.weightedDist (fun x => w x / s) u v := by
    have h1 := hsd
    rw [show Qspread G * s = s * Qspread G from by ring] at h1
    nlinarith
  linarith [Qspread_ge_of_feasible G hconn (fun x => w x / s) h_feasible_nn h_feasible_sum]

/-! ## Main Result -/

/-- **LP Strong Duality**: Qspread(G) = QDual(G) for connected graphs.
Proved using Farkas' lemma (geometric Hahn-Banach separation). -/
theorem lp_strong_duality
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hconn : G.Connected) :
    Qspread G = QDual G :=
  le_antisymm (weak_duality G hconn) (strong_duality G hconn)
