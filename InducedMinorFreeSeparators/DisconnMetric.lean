/-
# Disconnected Metric for G[S]

When G[S] is disconnected, define a PseudoMetricSpace on S that:
- Uses the G[S]-VWSP-light distance within each connected component
- Uses a large value M for cross-component pairs

This metric satisfies the hG_ball and hG_path conditions needed by pure_pairs_fat_model.
-/
import Mathlib
import InducedMinorFreeSeparators.VWSP
import InducedMinorFreeSeparators.CoarsePurePairs
import InducedMinorFreeSeparators.VWSPProperties
import InducedMinorFreeSeparators.ZHandling
import InducedMinorFreeSeparators.InducedMetricHelpers

open Set Function CoarsePurePairs SimpleGraph
open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Triangle inequality with reachability -/

omit [DecidableEq V] in
omit [Fintype V] in
lemma weightedDistLight_triangle_reachable
    {G : SimpleGraph V} {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {u v z : V} (huv : G.Reachable u v) (hvz : G.Reachable v z) :
    G.weightedDistLight w u z ≤ G.weightedDistLight w u v + G.weightedDistLight w v z := by
  rw [ weightedDistLight_eq_half, weightedDistLight_eq_half, weightedDistLight_eq_half ];
  rw [ ← add_div, div_le_div_iff_of_pos_right ] <;> norm_num;
  refine' le_of_forall_pos_le_add fun ε εpos => _;
  -- By definition of infimum, there exist walks p �1� and p2 such that p1.edgeWeightSum w ≤ G.weightedDist w u v + ε / 2 and p2.edgeWeightSum w ≤ G.weightedDist w v z + ε /  �2�.
  obtain ⟨p1, hp1⟩ : ∃ p1 : G.Walk u v, p1.edgeWeightSum w ≤ G.weightedDist w u v + ε / 2 := by
    have := exists_lt_of_csInf_lt ( show Set.Nonempty ( Set.range ( fun p : G.Walk u v => p.edgeWeightSum w ) ) from ⟨ _, ⟨ huv.some, rfl ⟩ ⟩ ) ( lt_add_of_pos_right _ ( half_pos εpos ) );
    exact Exists.elim this fun x hx => by rcases hx.1 with ⟨ p, rfl ⟩ ; exact ⟨ p, hx.2.le ⟩ ;
  obtain ⟨p2, hp2⟩ : ∃ p2 : G.Walk v z, p2.edgeWeightSum w ≤ G.weightedDist w v z + ε / 2 := by
    have := exists_lt_of_csInf_lt ( show Set.Nonempty ( Set.range fun p : G.Walk v z => p.edgeWeightSum w ) from ⟨ _, ⟨ hvz.some, rfl ⟩ ⟩ ) ( show InfSet.sInf ( Set.range fun p : G.Walk v z => p.edgeWeightSum w ) < InfSet.sInf ( Set.range fun p : G.Walk v z => p.edgeWeightSum w ) + ε / 2 from lt_add_of_pos_right _ ( half_pos εpos ) );
    exact Exists.elim this fun x hx => by rcases hx.1 with ⟨ p2, rfl ⟩ ; exact ⟨ p2, hx.2.le ⟩ ;
  exact le_trans ( ciInf_le ⟨ 0, Set.forall_mem_range.2 fun _ => edgeWeightSum_nonneg hw _ ⟩ ( p1.append p2 ) ) ( by linarith [ edgeWeightSum_append' w p1 p2 ] )

/-! ## Optimal walk exists for reachable pairs -/

lemma weightedDistLight_achieved_reachable
    {G : SimpleGraph V} {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {u v : V} (huv : G.Reachable u v) :
    ∃ (p : G.Walk u v), p.edgeWeightSumLight w = G.weightedDistLight w u v := by
  -- By definition of `weightedDistLight`, � there� exists a walk `p` from `u` to `v` such that `p.edgeWeightSumLight w ≤ G.weightedDistLight w u v`.
  obtain ⟨p, hp⟩ : ∃ p : G.Walk u v, p.length ≤ Fintype.card V ∧ ∀ q : G.Walk u v, q.length ≤ Fintype.card V → p.edgeWeightSumLight w ≤ q.edgeWeightSumLight w := by
    have h_finite : Set.Finite {p : G.Walk u v | p.length ≤ Fintype.card V} := by
      have h_finite_walks : ∀ n : ℕ, Set.Finite {p : G.Walk u v | p.length = n} := by
        intro n
        have h_finite_walks : Set.Finite {p : G.Walk u v | p.length = n} := by
          have h_finite_walks : ∀ n : ℕ, Set.Finite {p : G.Walk u v | p.length = n} := by
            intro n
            have h_finite_walks : ∀ n : ℕ, Set.Finite {p : G.Walk u v | p.length = n} := by
              intro n
              exact Set.toFinite {p : G.Walk u v | p.length = n}
            exact h_finite_walks n
          exact h_finite_walks n;
        exact h_finite_walks;
      exact Set.Finite.subset ( Set.Finite.biUnion ( Set.finite_le_nat ( Fintype.card V ) ) fun n hn => h_finite_walks n ) fun p hp => by aesop;
    apply_rules [ Set.exists_min_image ];
    obtain ⟨ p, hp ⟩ := huv.exists_isPath;
    exact ⟨ p, by simpa using hp.length_lt.le ⟩;
  -- By definition of `weightedDistLight`, we know that ` �p�` is a walk from `u` to `v` with the minimum edge weight sum.
  have h_min : ∀ q : G.Walk u v, p.edgeWeightSumLight w ≤ q.edgeWeightSumLight w := by
    intro q
    by_cases hq : q.length ≤ Fintype.card V
    · exact hp.right q hq
    ·
      refine' le_trans ( hp.2 ( q.bypass ) _ ) _;
      · have := q.bypass_isPath;
        have := this.length_lt;
        linarith;
      · rw [ edgeWeightSumLight_eq_half, edgeWeightSumLight_eq_half ];
        exact div_le_div_of_nonneg_right ( edgeWeightSum_bypass_le_vwsp hw q ) zero_le_two;
  exact ⟨ p, le_antisymm ( le_csInf ⟨ _, ⟨ p, rfl ⟩ ⟩ fun _ ⟨ q, hq ⟩ => hq ▸ h_min q ) ( csInf_le ⟨ 0, by rintro x ⟨ q, rfl ⟩ ; exact edgeWeightSumLight_nonneg hw q ⟩ ⟨ p, rfl ⟩ ) ⟩

/-! ## Geodesic properties for reachable pairs -/

omit [Fintype V] in
lemma optimal_walk_geodesic_reachable
    {G : SimpleGraph V} {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {x a : V} (_hxa : G.Reachable x a)
    (p : G.Walk x a) (hp : p.edgeWeightSumLight w = G.weightedDistLight w x a)
    {u : V} (hu : u ∈ p.support) :
    G.weightedDistLight w x u + G.weightedDistLight w u a =
    G.weightedDistLight w x a := by
  have h_split : p.edgeWeightSumLight w = (p.takeUntil u hu).edgeWeightSumLight w + (p.dropUntil u hu).edgeWeightSumLight w := 
by
    convert edgeWeightSumLight_eq_half w ( p.takeUntil u hu |> Walk.append <| p.dropUntil u hu ) using 1;
    · rw [ SimpleGraph.Walk.take_spec ];
    · rw [ edgeWeightSum_append', edgeWeightSumLight_eq_half, edgeWeightSumLight_eq_half ] ; ring;
  refine' le_antisymm _ _;
  · have h_triangle : ∀ (v z : V) (p : G.Walk v z), p.edgeWeightSumLight w ≥ G.weightedDistLight w v z := by
      exact fun v z p => ciInf_le ⟨ 0, Set.forall_mem_range.mpr fun q => edgeWeightSumLight_nonneg hw q ⟩ p;
    linarith [ h_triangle x u ( p.takeUntil u hu ), h_triangle u a ( p.dropUntil u hu ) ];
  · apply_rules [ weightedDistLight_triangle_reachable ];
    · exact ⟨ p.takeUntil u hu ⟩;
    · exact ⟨ p.dropUntil u hu ⟩

omit [Fintype V] in
lemma optimal_walk_in_ball_reachable
    {G : SimpleGraph V} {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {x a : V} (hxa : G.Reachable x a)
    (p : G.Walk x a) (hp : p.edgeWeightSumLight w = G.weightedDistLight w x a)
    {u : V} (hu : u ∈ p.support) :
    G.weightedDistLight w x u ≤ G.weightedDistLight w x a := by
  by_contra! h_contra;
  exact h_contra.not_ge ( by linarith [ optimal_walk_geodesic_reachable hw hxa p hp hu, show 0 ≤ G.weightedDistLight w u a from by
                                                                                          apply Real.iInf_nonneg;
                                                                                          grind +suggestions ] ) ;

/-! ## Max distance within a component -/

omit [DecidableEq V] in
lemma max_component_dist_le
    {G : SimpleGraph V} {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {δ : ℝ} (hδ : 0 ≤ δ) (hS : ∀ v, w v ≤ δ)
    {x y : V} (hxy : G.Reachable x y) :
    G.weightedDistLight w x y ≤ (Fintype.card V : ℝ) * δ := by
  obtain ⟨p, hp⟩ : ∃ p : G.Walk x y, p.IsPath := by
    obtain ⟨ p, hp ⟩ := hxy.exists_isPath; exact ⟨ p, hp ⟩ ;
  refine' le_trans _ _;
  exact p.edgeWeightSumLight w;
  · exact csInf_le ⟨ 0, by
      rintro _ ⟨ p, rfl ⟩;
      grind +suggestions ⟩ ⟨ p, rfl ⟩;
  · refine' le_trans _ ( mul_le_mul_of_nonneg_right ( show ( p.length : ℝ ) + 1 ≤ Fintype.card V from mod_cast _ ) hδ );
    · induction p <;> simp_all +decide [ Walk.edgeWeightSumLight ];
      rename_i u v w huv p ih;
      linarith [ hS u, hS v, ih ( by exact p.reachable ) ];
    · have := hp.support_nodup.length_le_card;
      cases p <;> aesop

/-! ## The disconnected metric -/

/-- Distance function for the disconnected metric on S.
    Within a component: G[S]-VWSP-light distance.
    Across components: M (a large value). -/
def disconnDist
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) (w : V → ℝ)
    (M : ℝ) (x y : S) : ℝ :=
  if (G.comap (Subtype.val : S → V)).Reachable x y then
    (G.comap (Subtype.val : S → V)).weightedDistLight (w ∘ Subtype.val) x y
  else M

lemma disconnDist_self
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Set V} {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {M : ℝ} (x : S) :
    disconnDist G S w M x x = 0 := by
  unfold disconnDist;
  simp +decide [ weightedDistLight_eq_half ];
  grind +suggestions

lemma disconnDist_comm
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Set V} {w : V → ℝ}
    {M : ℝ} (x y : S) :
    disconnDist G S w M x y = disconnDist G S w M y x := by
  simp only [disconnDist]
  by_cases h : (G.comap (Subtype.val : S → V)).Reachable x y
  · rw [if_pos h, if_pos h.symm, weightedDistLight_eq_half, weightedDistLight_eq_half,
      weightedDist_symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

lemma disconnDist_triangle
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Set V} {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {δ : ℝ} (hδ : 0 ≤ δ) (hS : ∀ v ∈ S, w v ≤ δ)
    {M : ℝ} (hM : (Fintype.card S : ℝ) * δ ≤ M)
    (x y z : S) :
    disconnDist G S w M x z ≤ disconnDist G S w M x y + disconnDist G S w M y z := by
  by_cases hxy : (G.comap (Subtype.val : S → V)).Reachable x y;
  · by_cases hyz : (G.comap (Subtype.val : S → V)).Reachable y z <;> simp_all +decide [ disconnDist ];
    · rw [ if_pos ( hxy.trans hyz ) ];
      convert weightedDistLight_triangle_reachable ( fun v => hw v.val ) hxy hyz using 1;
    · split_ifs;
      · exact False.elim ( hyz <| hxy.symm.trans ‹_› );
      · exact le_add_of_nonneg_left ( by exact Real.iInf_nonneg fun _ => by exact edgeWeightSumLight_nonneg ( fun _ => hw _ ) _ );
  · by_cases hxz : ( G.comap ( Subtype.val : S → V ) ).Reachable x z <;> simp_all +decide [ disconnDist ];
    · refine' le_trans _ ( le_add_of_nonneg_right _ );
      · refine' le_trans _ hM;
        convert max_component_dist_le ( show ∀ v : S, 0 ≤ w v from fun v => hw v ) hδ ( fun v => hS v v.2 ) hxz using 1;
        rw [ Fintype.card_of_subtype ] ; aesop;
      · split_ifs;
        · apply Real.iInf_nonneg; intro p; exact edgeWeightSumLight_nonneg (fun v => hw v.val) p;
        · exact le_trans ( mul_nonneg ( Nat.cast_nonneg _ ) hδ ) hM;
    · split_ifs;
      · apply Real.iInf_nonneg; intro p; exact (by
        apply edgeWeightSumLight_nonneg; exact fun v => hw v.val;);
      · exact le_trans ( mul_nonneg ( Nat.cast_nonneg _ ) hδ ) hM

/-- The PseudoMetricSpace on S using the disconnected metric. -/
noncomputable def disconnPMS
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (δ : ℝ) (hδ : 0 ≤ δ) (hS : ∀ v ∈ S, w v ≤ δ)
    (M : ℝ) (hM : (Fintype.card S : ℝ) * δ ≤ M) : PseudoMetricSpace S :=
  mkPMS (disconnDist G S w M)
    (fun x => disconnDist_self hw x)
    (fun x y => disconnDist_comm x y)
    (fun x y z => disconnDist_triangle hw hδ hS hM x y z)

/-! ## Key properties of the disconnected metric -/

/-
Adjacent vertices in G[S] have disconnDist ≤ δ.
-/
lemma disconn_adj_dist_le
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Set V} {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {δ : ℝ} (hS : ∀ v ∈ S, w v ≤ δ)
    {M : ℝ} {x y : S}
    (hadj : (G.comap (Subtype.val : S → V)).Adj x y) :
    disconnDist G S w M x y ≤ δ := by
  unfold disconnDist;
  rw [ if_pos ( SimpleGraph.Adj.reachable hadj ) ];
  refine' le_trans ( weightedDistLight_le_edge _ _ ) _;
  · exact fun v => hw _;
  · exact hadj;
  · linarith! [ hS x x.2, hS y y.2 ]

/-
If disconnDist > δ, then G-light distance > δ.
-/
lemma disconnDist_gt_implies_G_light_gt
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Set V} {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (hconn : G.Connected)
    {δ : ℝ} (_hδ : 0 ≤ δ) (hS : ∀ v ∈ S, w v ≤ δ) (hS' : ∀ v, w v ≤ δ → v ∈ S)
    {M : ℝ} (_hM : δ < M)
    {x y : S}
    (hd : δ < disconnDist G S w M x y) :
    δ < G.weightedDistLight w x.val y.val := by
  contrapose! hd;
  obtain ⟨ p, hp ⟩ := weightedDistLight_achieved hw hconn x.val y.val;
  -- By walk_lift_to_subgraph, this walk lifts to G.comap Subtype.val, giving a walk from x to y in G[S] with the same weight.
  obtain ⟨p', hp'⟩ : ∃ p' : (G.comap (Subtype.val : S → V)).Walk x y, p'.edgeWeightSumLight (w ∘ Subtype.val) = p.edgeWeightSumLight w := by
    have h_walk_support : ∀ v ∈ p.support, v ∈ S := by
      intro v hv; exact hS' v (walk_support_weight_le hw p (by linarith) (hS x x.2) (hS y y.2) hv) ;
    exact ⟨ Classical.choose ( walk_lift_to_subgraph x.2 y.2 p h_walk_support ), Classical.choose_spec ( walk_lift_to_subgraph x.2 y.2 p h_walk_support ) w ⟩;
  unfold disconnDist;
  split_ifs <;> simp_all +decide [ SimpleGraph.Reachable ];
  · refine' le_trans _ hd;
    exact hp'.symm ▸ ciInf_le ⟨ 0, Set.forall_mem_range.2 fun _ => edgeWeightSumLight_nonneg ( fun _ => hw _ ) _ ⟩ _;
  · exact False.elim ( ‹IsEmpty ( SimpleGraph.Walk ( SimpleGraph.comap Subtype.val G ) x y ) ›.elim p' )

/-
disconnDist ≥ G-light distance for within-component pairs.
-/
lemma disconnDist_ge_G_light
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Set V} {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (_hconn : G.Connected)
    {M : ℝ} (_hM : 0 ≤ M) {x y : S}
    (hreach : (G.comap (Subtype.val : S → V)).Reachable x y) :
    G.weightedDistLight w x.val y.val ≤ disconnDist G S w M x y := by
  -- By definition of `disconnDist`, since `hreach` holds, we have `disconnDist G S w M x y = (G.comap Subtype.val).weightedDistLight (w ∘ Subtype.val) x y`.
  have h_disconnDist : disconnDist G S w M x y = (G.comap Subtype.val).weightedDistLight (w ∘ Subtype.val) x y := by
    exact if_pos hreach;
  refine' h_disconnDist ▸ le_csInf _ _ <;> norm_num +zetaDelta at *;
  · exact ⟨ _, ⟨ hreach.some, rfl ⟩ ⟩;
  · intro p;
    refine' le_trans ( ciInf_le _ _ ) _;
    exact ⟨ 0, Set.forall_mem_range.2 fun p => edgeWeightSumLight_nonneg hw p ⟩;
    exact p.map ( SimpleGraph.Hom.comap _ _ );
    induction p <;> simp +decide [ *, Walk.edgeWeightSumLight ];
    rename_i u v w huv p ih;
    exact ih ( SimpleGraph.Walk.reachable p ) ( by
      exact if_pos ( by exact p.reachable ) )

/-! ## dist = disconnDist in disconnPMS -/

@[simp]
lemma disconnPMS_dist_eq
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Set V} {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {δ : ℝ} (hδ : 0 ≤ δ) (hS : ∀ v ∈ S, w v ≤ δ)
    {M : ℝ} (hM : (Fintype.card S : ℝ) * δ ≤ M)
    (x y : S) :
    @dist S (disconnPMS G S w hw δ hδ hS M hM).toDist x y = disconnDist G S w M x y := rfl

lemma disconnDist_lt_M_iff_reachable
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Set V} {w : V → ℝ}
    {M : ℝ} {x y : S} :
    disconnDist G S w M x y < M ↔
    (G.comap (Subtype.val : S → V)).Reachable x y ∧
    (G.comap (Subtype.val : S → V)).weightedDistLight (w ∘ Subtype.val) x y < M := by
  simp only [disconnDist]
  split
  · exact ⟨fun h => ⟨‹_›, h⟩, fun h => h.2⟩
  · exact ⟨fun h => absurd h (lt_irrefl _), fun ⟨hr, _⟩ => absurd hr ‹_›⟩

lemma disconnDist_of_reachable
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Set V} {w : V → ℝ}
    {M : ℝ} {x y : S}
    (h : (G.comap (Subtype.val : S → V)).Reachable x y) :
    disconnDist G S w M x y =
    (G.comap (Subtype.val : S → V)).weightedDistLight (w ∘ Subtype.val) x y := by
  simp [disconnDist, h]

lemma reachable_of_disconnDist_le
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Set V} {w : V → ℝ}
    {M : ℝ} {x y : S} {r : ℝ} (hr : r < M)
    (h : disconnDist G S w M x y ≤ r) :
    (G.comap (Subtype.val : S → V)).Reachable x y := by
  by_contra hn
  simp [disconnDist, hn] at h
  linarith

omit [Fintype V] in
lemma walk_reachable_on_support
    {G : SimpleGraph V} {x y : V} (p : G.Walk x y)
    {u : V} (hu : u ∈ p.support) : G.Reachable x u :=
  ⟨p.takeUntil u hu⟩

omit [Fintype V] in
lemma walk_reachable_on_support'
    {G : SimpleGraph V} {x y : V} (p : G.Walk x y)
    {u : V} (hu : u ∈ p.support) : G.Reachable u y :=
  ⟨p.dropUntil u hu⟩

/-! ## hG_ball for the disconnected metric -/

theorem disconn_hG_ball
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Set V} {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (_hconn : G.Connected)
    {δ : ℝ} (hδ : 0 ≤ δ) (hS : ∀ v ∈ S, w v ≤ δ) (_hS' : ∀ v, w v ≤ δ → v ∈ S)
    {M : ℝ} (hM_bound : (Fintype.card S : ℝ) * δ ≤ M) (hM_pos : δ < M)
    (A : Set S) :
    @deltaConnected S (disconnPMS G S w hw δ hδ hS M hM_bound) δ A →
    graphSetConnected (G.comap (Subtype.val : S → V))
      (@setBall S (disconnPMS G S w hw δ hδ hS M hM_bound) A (δ / 2)) := by
  intro hA
  set G' := G.comap (Subtype.val : S → V)
  set pms := disconnPMS G S w hw δ hδ hS M hM_bound
  have hw' : ∀ v : S, 0 ≤ (w ∘ Subtype.val) v := fun v => hw v.val
  -- Every element of setBall is G'-reachable from some element of A
  have hball_reach : ∀ y ∈ @setBall S pms A (δ / 2), ∃ a ∈ A, G'.Reachable a y := by
    intro y hy
    obtain ⟨a, haA, had⟩ := hy
    exact ⟨a, haA, reachable_of_disconnDist_le (by linarith) had⟩
  -- All elements of A are G'-reachable from each other (via chain connectivity)
  have chain_reachable : ∀ a₁ a₂ : S,
      Relation.ReflTransGen (@chainRel S pms A δ) a₁ a₂ → G'.Reachable a₁ a₂ := by
    intro a₁ a₂ hchain
    induction hchain with
    | refl => exact ⟨Walk.nil⟩
    | @tail b c _ hbc ih =>
      exact ih.trans (reachable_of_disconnDist_le (by linarith) hbc.2.2)
  have hA_reach : ∀ a₁ ∈ A, ∀ a₂ ∈ A, G'.Reachable a₁ a₂ :=
    fun a₁ ha₁ a₂ ha₂ => chain_reachable a₁ a₂ (hA.2 a₁ ha₁ a₂ ha₂)
  set B := @setBall S pms A (δ / 2)
  -- Helper: walk from a ∈ A to x with d(a,x) ≤ δ/2 stays in setBall
  have walk_in_ball : ∀ (a : S), a ∈ A → ∀ (x : S),
      G'.Reachable a x → G'.weightedDistLight (w ∘ Subtype.val) a x ≤ δ / 2 →
      Relation.ReflTransGen (fun u v => u ∈ B ∧ v ∈ B ∧ G'.Adj u v) a x := by
    intro a haA x hreach hdist
    obtain ⟨p, hp⟩ := weightedDistLight_achieved_reachable hw' hreach
    apply walk_connected_in_set p
    intro u hu
    refine ⟨a, haA, ?_⟩
    rw [disconnPMS_dist_eq, disconnDist_of_reachable (walk_reachable_on_support p hu)]
    exact le_trans (optimal_walk_in_ball_reachable hw' hreach p hp hu) hdist
  -- Helper: walk between chain-connected A elements stays in setBall
  have chain_in_ball : ∀ (a b : S), a ∈ A → b ∈ A →
      G'.Reachable a b → disconnDist G S w M a b ≤ δ →
      Relation.ReflTransGen (fun u v => u ∈ B ∧ v ∈ B ∧ G'.Adj u v) a b := by
    intro a b haA hbA hreach hdist
    have hdist' : G'.weightedDistLight (w ∘ Subtype.val) a b ≤ δ := by
      rw [← disconnDist_of_reachable hreach]; exact hdist
    obtain ⟨p, hp⟩ := weightedDistLight_achieved_reachable hw' hreach
    apply walk_connected_in_set p
    intro u hu
    have hgeo := optimal_walk_geodesic_reachable hw' hreach p hp hu
    have _ := optimal_walk_in_ball_reachable hw' hreach p hp hu
    by_cases hle : G'.weightedDistLight (w ∘ Subtype.val) a u ≤ δ / 2
    · refine ⟨a, haA, ?_⟩
      rw [disconnPMS_dist_eq, disconnDist_of_reachable (walk_reachable_on_support p hu)]
      exact hle
    · push_neg at hle
      have : G'.weightedDistLight (w ∘ Subtype.val) u b ≤ δ / 2 := by linarith
      refine ⟨b, hbA, ?_⟩
      rw [disconnPMS_dist_eq, disconnDist_comm b u, disconnDist_of_reachable (walk_reachable_on_support' p hu)]
      exact this
  -- Helper: chain-connected A elements connected through setBall
  have chain_through_ball : ∀ (a₁ a₂ : S), a₁ ∈ A → a₂ ∈ A →
      Relation.ReflTransGen (@chainRel S pms A δ) a₁ a₂ →
      Relation.ReflTransGen (fun u v => u ∈ B ∧ v ∈ B ∧ G'.Adj u v) a₁ a₂ := by
    intro a₁ a₂ ha₁ ha₂ hchain
    induction hchain with
    | refl => exact .refl
    | @tail b c _ hbc ih =>
      have hbA := hbc.1
      have hcA := hbc.2.1
      have hdist := hbc.2.2
      have hreach_bc := reachable_of_disconnDist_le (by linarith) hdist
      exact (ih hbA).trans (chain_in_ball b c hbA hcA hreach_bc hdist)
  constructor
  -- Nonemptiness
  · obtain ⟨a₀, ha₀⟩ := hA.1
    exact ⟨a₀, a₀, ha₀, by rw [disconnPMS_dist_eq, disconnDist_self hw]; linarith⟩
  -- Connectivity
  · intro x hx y hy
    obtain ⟨ax, haxA, hax_dist⟩ := hx
    obtain ⟨ay, hayA, hay_dist⟩ := hy
    have hax_reach := reachable_of_disconnDist_le (by linarith) hax_dist
    have hay_reach := reachable_of_disconnDist_le (by linarith) hay_dist
    -- x to ax (reverse the walk from ax to x)
    have hx_ax : Relation.ReflTransGen (fun u v => u ∈ B ∧ v ∈ B ∧ G'.Adj u v) x ax := by
      have hax_wdist : G'.weightedDistLight (w ∘ Subtype.val) ax x ≤ δ / 2 := by
        rw [← disconnDist_of_reachable hax_reach]; exact hax_dist
      have h := walk_in_ball ax haxA x hax_reach hax_wdist
      exact Relation.ReflTransGen.symmetric (fun _ _ ⟨h1, h2, h3⟩ => ⟨h2, h1, h3.symm⟩) h
    -- ax to ay (chain through A)
    have hax_ay := chain_through_ball ax ay haxA hayA (hA.2 ax haxA ay hayA)
    -- ay to y
    have hay_wdist : G'.weightedDistLight (w ∘ Subtype.val) ay y ≤ δ / 2 := by
      rw [← disconnDist_of_reachable hay_reach]; exact hay_dist
    have hay_y := walk_in_ball ay hayA y hay_reach hay_wdist
    exact hx_ax.trans (hax_ay.trans hay_y)

/-! ## hG_path for the disconnected metric -/

set_option maxHeartbeats 400000 in
theorem disconn_hG_path
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Set V} {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (_hconn : G.Connected)
    {δ : ℝ} (hδ : 0 ≤ δ) (hS : ∀ v ∈ S, w v ≤ δ) (_hS' : ∀ v, w v ≤ δ → v ∈ S)
    {M : ℝ} (hM_bound : (Fintype.card S : ℝ) * δ ≤ M) (hM_pos : 5 * δ < M)
    (x : S) (A : Set S) (r : ℝ) :
    A.Nonempty →
    r ≤ 5 * δ →
    (∃ a ∈ A, @dist S (disconnPMS G S w hw δ hδ hS M hM_bound).toDist x a ≤ r) →
    ∃ (P : Set S) (a : S), a ∈ A ∩ P ∧ x ∈ P ∧
      graphSetConnected (G.comap (Subtype.val : S → V)) P ∧
      P ⊆ @setBall S (disconnPMS G S w hw δ hδ hS M hM_bound) {x} r ∧
      ∀ u ∈ P, @dist S (disconnPMS G S w hw δ hδ hS M hM_bound).toDist x u +
        @dist S (disconnPMS G S w hw δ hδ hS M hM_bound).toDist u a =
        @dist S (disconnPMS G S w hw δ hδ hS M hM_bound).toDist x a := by
  intro _hA hr ⟨a₀, ha₀A, ha₀⟩
  set G' := G.comap (Subtype.val : S → V)
  have hw' : ∀ v : S, 0 ≤ (w ∘ Subtype.val) v := fun v => hw v.val
  -- a₀ is reachable from x (since dist ≤ r < M)
  have hreach : G'.Reachable x a₀ := reachable_of_disconnDist_le (by linarith) ha₀
  -- Get optimal walk
  obtain ⟨p, hp⟩ := weightedDistLight_achieved_reachable hw' hreach
  -- The walk weight equals disconnDist(x, a₀)
  have hdist_eq : disconnDist G S w M x a₀ = G'.weightedDistLight (w ∘ Subtype.val) x a₀ :=
    disconnDist_of_reachable hreach
  use p.support.toFinset, a₀
  refine ⟨⟨ha₀A, List.mem_toFinset.mpr (Walk.end_mem_support p)⟩,
    List.mem_toFinset.mpr (Walk.start_mem_support p), ?_, ?_, ?_⟩
  -- graphSetConnected
  · exact walk_support_graphSetConnected p
  -- P ⊆ setBall
  · intro u hu
    simp only [setBall, Set.mem_setOf_eq]
    use x, Set.mem_singleton x
    rw [Finset.mem_coe, List.mem_toFinset] at hu
    have hxu := walk_reachable_on_support p hu
    rw [disconnPMS_dist_eq, disconnDist_of_reachable hxu]
    calc G'.weightedDistLight (w ∘ Subtype.val) x u
        ≤ G'.weightedDistLight (w ∘ Subtype.val) x a₀ :=
          optimal_walk_in_ball_reachable hw' hreach p hp hu
      _ = disconnDist G S w M x a₀ := hdist_eq.symm
      _ ≤ r := ha₀
  -- Geodesic
  · intro u hu
    rw [Finset.mem_coe, List.mem_toFinset] at hu
    have hxu := walk_reachable_on_support p hu
    have hua := walk_reachable_on_support' p hu
    simp only [disconnPMS_dist_eq, disconnDist_of_reachable hxu,
      disconnDist_of_reachable hua, disconnDist_of_reachable hreach]
    exact optimal_walk_geodesic_reachable hw' hreach p hp hu

end
