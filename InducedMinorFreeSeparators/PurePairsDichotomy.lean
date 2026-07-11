/-
# Pure Pairs Dichotomy

Bridge between internal proof machinery and the user-facing `ContainsInducedMinor`/`oneSubdivision`
definitions, plus the main `pure_pairs_dichotomy` theorem.
-/
import Mathlib
import InducedMinorFreeSeparators.ProofDefs
import InducedMinorFreeSeparators.VWSP
import InducedMinorFreeSeparators.CoarsePurePairs
import InducedMinorFreeSeparators.VWSPProperties
import InducedMinorFreeSeparators.ZHandling
import InducedMinorFreeSeparators.ZSmallConnected
import InducedMinorFreeSeparators.InducedMetricHelpers
import InducedMinorFreeSeparators.DisconnMetric

open Set Function CoarsePurePairs SimpleGraph
open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V]

/-! ## Bridge: internal induced minor ↔ ContainsInducedMinor -/

/-- Bridge from internal induced minor model to `ContainsInducedMinor`. -/
theorem hasInducedMinor_internal_to_containsInducedMinor
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (h : HasInducedMinor_internal G H) :
    G.ContainsInducedMinor H := by
  obtain ⟨m⟩ := h
  exact ⟨m.branch,
    fun w => by
      have hc := m.branch_connected w
      obtain ⟨⟨v, hv⟩⟩ := hc.nonempty
      exact ⟨v, hv⟩,
    m.branch_connected,
    m.branch_disjoint,
    m.adj_preserved,
    m.nonadj_preserved⟩

/-- The converse: `ContainsInducedMinor` implies `HasInducedMinor_internal`. -/
theorem containsInducedMinor_to_hasInducedMinor_internal
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (h : G.ContainsInducedMinor H) :
    HasInducedMinor_internal G H := by
  obtain ⟨φ, _, hconn, hdisj, hadj, hnadj⟩ := h
  exact ⟨⟨φ, hconn, hdisj, hadj, hnadj⟩⟩

/-! ## Bridge: graphOneSubdiv (completeGraph (Fin h)) and oneSubdivision h -/

def kedgeToEdgeSet (h : ℕ) : KEdge h → (completeGraph (Fin h)).edgeSet :=
  fun ⟨⟨i, j⟩, hij⟩ => ⟨Sym2.mk (i, j), by simp [completeGraph]; exact ne_of_lt hij⟩

lemma hasInducedMinor_graphOneSubdiv_to_oneSubdivision
    {V : Type*} (G : SimpleGraph V) (h : ℕ) :
    HasInducedMinor_internal G (graphOneSubdiv (completeGraph (Fin h))) →
    G.ContainsInducedMinor (oneSubdivision h) := by
  intro h
  obtain ⟨φ, h_connected, h_disjoint, h_adj⟩ := h
  use fun v => match v with
    | Sum.inl i => φ (Sum.inl i)
    | Sum.inr ⟨⟨i, j⟩, hij⟩ => φ (Sum.inr ⟨Sym2.mk (i, j), by simp [completeGraph]; exact ne_of_lt hij⟩);
  refine' ⟨ _, _, _, _, _ ⟩;
  · intro w;
    rcases w with ( i | ⟨ ⟨ i, j ⟩, hij ⟩ ) <;> simp +decide [ SimpleGraph.connected_induce_iff ] at h_connected ⊢;
    · exact h_connected.1 i |> fun h => h.nonempty;
    · have := h_connected.2 ( s(i, j) ) ( by simpa [ Sym2.eq ] using hij.ne ) ; exact this.nonempty;
  · intro w; cases w <;> tauto;
  · grind;
  · rintro ( i | ⟨ ⟨ i, j ⟩, hij ⟩ ) ( k | ⟨ ⟨ k, l ⟩, hkl ⟩ ) <;> simp +decide [ oneSubdivision ];
    · tauto;
    · convert h_adj ( Sum.inl i ) ( Sum.inr ⟨ Sym2.mk ( k, l ), by simp [ completeGraph ] ; exact ne_of_lt hkl ⟩ ) using 1;
      simp +decide [ graphOneSubdiv ];
      exact ⟨ fun h => by cases h <;> tauto, fun h => by cases h <;> tauto ⟩;
    · intro hk; cases hk <;> simp +decide [ *, graphOneSubdiv ];
    · exact fun h => False.elim <| h;
  · rintro ( i | ⟨ ⟨ i, j ⟩, hij ⟩ ) ( k | ⟨ ⟨ k, l ⟩, hkl ⟩ ) <;> simp +decide [ oneSubdivision ];
    · rename_i h';
      exact fun hi hk v₁ hv₁ v₂ hv₂ => h' _ _ ( by simpa [ Sum.inl.injEq ] using hi ) ( by simp [ graphOneSubdiv ] ) _ hv₁ _ hv₂;
    · rename_i h;
      convert h ( Sum.inl i ) ( Sum.inr ⟨ s(k, l), by simp [ completeGraph ] ; exact ne_of_lt hkl ⟩ ) _ using 1;
      · simp +decide [ graphOneSubdiv ];
        exact ⟨ fun h => ⟨ by rintro rfl; exact h ( Or.inl rfl ), by rintro rfl; exact h ( Or.inr rfl ) ⟩, fun h => by rintro ( h' | h' ) <;> tauto ⟩;
      · grind;
    · rename_i h';
      intro h'' v₁ hv₁ v₂ hv₂;
      convert h' _ _ _ _ v₁ hv₁ v₂ hv₂ using 1;
      · grind;
      · convert h'' using 1;
        simp +decide [ graphOneSubdiv ];
        exact ⟨ fun h => by tauto, fun h => by tauto ⟩;
    · intro h₁ h₂ v₁ hv₁ v₂ hv₂;
      rename_i h;
      convert h _ _ _ _ v₁ hv₁ v₂ hv₂ using 1;
      · grind;
      · finiteness

/-! ## Heavy/Light metric conversion -/

lemma vwspPMS_dist_eq_two_vwspPMSLight_dist
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hconn : G.Connected) (x y : V) :
    @dist V (vwspPMS G w hw hconn).toDist x y =
    2 * @dist V (vwspPMSLight G w hw hconn).toDist x y := by
  simp only [vwspPMS, vwspPMSLight, mkPMS, weightedDistLight_eq_half]; ring

lemma pairDistSum_heavy_eq_two_light
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hconn : G.Connected) :
    @pairDistSum V _ (vwspPMS G w hw hconn) =
    2 * @pairDistSum V _ (vwspPMSLight G w hw hconn) := by
  simp only [pairDistSum]
  rw [Finset.mul_sum]; congr 1; ext x; rw [Finset.mul_sum]; congr 1; ext y
  exact vwspPMS_dist_eq_two_vwspPMSLight_dist G w hw hconn x y

/-! ## Helper lemmas for the dichotomy -/

lemma pure_pairs_dichotomy_small_n
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ℕ) (hh : 2 ≤ h) (hconn : G.Connected)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hn : 0 < Fintype.card V)
    (hsmall : (Fintype.card V : ℝ) ≤ 32 * (h : ℝ) ^ 2) :
    let pms := vwspPMS G w hw hconn
    let n := (Fintype.card V : ℝ)
    let D := @pairDistSum V _ pms
    (∃ (x₀ : V) (S : Finset V), x₀ ∈ S ∧
      (∀ s ∈ S, @dist V pms.toDist x₀ s ≤ D / (n ^ 2 * 3)) ∧
      (1 : ℝ) / (32 * (h : ℝ) ^ 2) * n ≤ S.card) := by
  refine' ⟨ Classical.choose ( Finset.card_pos.mp hn ), { Classical.choose ( Finset.card_pos.mp hn ) }, _, _, _ ⟩ <;> norm_num;
  · refine' div_nonneg _ _;
    · apply Finset.sum_nonneg; intro x _; apply Finset.sum_nonneg; intro y _; exact (by
      exact Real.iInf_nonneg fun _ => edgeWeightSum_nonneg hw _);
    · positivity;
  · rw [ inv_mul_eq_div, div_mul_eq_mul_div, div_le_iff₀ ] <;> nlinarith [ show ( h : ℝ ) ≥ 2 by norm_cast ]

lemma pure_pairs_dichotomy_D_zero
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ℕ) (hh : 2 ≤ h) (hconn : G.Connected)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hn : 0 < Fintype.card V)
    (hD : @pairDistSum V _ (vwspPMS G w hw hconn) = 0) :
    let pms := vwspPMS G w hw hconn
    let n := (Fintype.card V : ℝ)
    let D := @pairDistSum V _ pms
    (∃ (x₀ : V) (S : Finset V), x₀ ∈ S ∧
      (∀ s ∈ S, @dist V pms.toDist x₀ s ≤ D / (n ^ 2 * 3)) ∧
      (1 : ℝ) / (32 * (h : ℝ) ^ 2) * n ≤ S.card) := by
  refine' ⟨ Classical.choose ( Finset.card_pos.mp hn ), Finset.univ, _, _, _ ⟩ <;> simp +decide [ hD ];
  · intro s; exact (by
    contrapose! hD;
    refine' ne_of_gt ( lt_of_lt_of_le _ ( Finset.single_le_sum ( fun x _ => Finset.sum_nonneg fun y _ => _ ) ( Finset.mem_univ ( Classical.choose ( Finset.card_pos.mp hn ) ) ) |> le_trans ( Finset.single_le_sum ( fun y _ => _ ) ( Finset.mem_univ s ) ) ) ) <;> simp_all +decide);
  · exact mul_le_of_le_one_left ( Nat.cast_nonneg _ ) ( mul_le_one₀ ( inv_le_one_of_one_le₀ ( one_le_pow₀ ( by norm_cast; linarith ) ) ) ( by norm_num ) ( by norm_num ) )

lemma completeGraph_edgeSet_ncard (k : ℕ) :
    (completeGraph (Fin k)).edgeSet.ncard = k * (k - 1) / 2 := by
  rw [ Set.ncard_eq_toFinset_card' ] ; norm_num [ Finset.card_univ, Finset.card_singleton ] ; ring_nf;
  rw [ Finset.card_compl ];
  rcases k with ( _ | _ | k ) <;> simp +arith +decide;
  rw [ show ( Finset.filter ( Membership.mem Sym2.diagSet ) Finset.univ : Finset ( Sym2 ( Fin ( k + 2 ) ) ) ) = Finset.image ( fun x : Fin ( k + 2 ) => Sym2.mk ( x, x ) ) Finset.univ from ?_, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
  · rw [ Sym2.card ] ; norm_num [ Nat.choose_two_right ] ; ring_nf; omega;
  · ext ⟨ x, y ⟩ ; aesop

lemma parameter_feasibility (h : ℕ) (hh : 2 ≤ h) :
    (2 * (h : ℝ) + 2) * (13 / (40 * (h : ℝ))) +
    ((h : ℝ) + (h : ℝ) * ((h : ℝ) - 1) / 2) * (1 / (32 * (h : ℝ) ^ 2)) < 1 := by
  field_simp; nlinarith [ ( by norm_cast : ( 2 : ℝ ) ≤ h ) ]

def countingFinOuterMeasure [Fintype V] (hn : 0 < Fintype.card V) :
    FinOuterMeasure V where
  toFun S := (S.toFinset.card : ℝ) / (Fintype.card V : ℝ)
  empty := by simp
  mono h := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Finset.card_le_card (Set.toFinset_mono h)
  union_le X Y := by
    have hc : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
    simp only [Set.toFinset_union]
    calc (↑(X.toFinset ∪ Y.toFinset).card : ℝ) / ↑(Fintype.card V)
        ≤ (↑X.toFinset.card + ↑Y.toFinset.card) / ↑(Fintype.card V) := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hc)
          exact_mod_cast Finset.card_union_le _ _
      _ = _ := by ring

omit [Fintype V] in
lemma countingFinOuterMeasure_univ [Fintype V] (hn : 0 < Fintype.card V) :
    (countingFinOuterMeasure hn).toFun Set.univ = 1 := by
  unfold countingFinOuterMeasure; aesop

/-! ## The core Z-handling theorem -/

set_option maxHeartbeats 800000 in
theorem pure_pairs_vwsp_dichotomy
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ℕ) (hh : 2 ≤ h) (hconn : G.Connected)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hn : 0 < Fintype.card V)
    (hnlarge : 32 * (h : ℝ) ^ 2 < (Fintype.card V : ℝ)) :
    let pms := vwspPMS G w hw hconn
    let n := (Fintype.card V : ℝ)
    let D := @pairDistSum V _ pms
    (∃ (x₀ : V) (S : Finset V), x₀ ∈ S ∧
      (∀ s ∈ S, @dist V pms.toDist x₀ s ≤ D / (n ^ 2 * 3)) ∧
      (1 : ℝ) / (32 * (h : ℝ) ^ 2) * n ≤ S.card) ∨
    (∃ (A B : Finset V),
      (13 : ℝ) / (40 * (h : ℝ)) * n ≤ A.card ∧
      (13 : ℝ) / (40 * (h : ℝ)) * n ≤ B.card ∧
      ∀ b ∈ B, D / (n ^ 2 * 33) ≤
        @Metric.infDist V pms b (↑A : Set V)) ∨
    HasInducedMinor_internal G (graphOneSubdiv (completeGraph (Fin h))) := by
  intro pms n D
  set D_light := @pairDistSum V _ (vwspPMSLight G w hw hconn) with hDL_def
  set δ₀ := D_light / (n ^ 2 * 33) with hδ₀_def
  have hD_eq : D = 2 * D_light := pairDistSum_heavy_eq_two_light G w hw hconn
  have hδ₀_nonneg : 0 ≤ δ₀ := by
    apply div_nonneg
    · apply Finset.sum_nonneg; intro x _; apply Finset.sum_nonneg; intro y _
      simp only [vwspPMSLight, mkPMS]
      exact Real.iInf_nonneg fun p => edgeWeightSumLight_nonneg hw p
    · positivity
  set Z := Finset.filter (fun v => δ₀ < w v) Finset.univ with hZ_def
  have hZ_far : ∀ a ∈ Z, ∀ b ∈ Z, a ≠ b →
      δ₀ < @dist V (vwspPMSLight G w hw hconn).toDist a b := by
    intro a ha b hb hab; simp [hZ_def] at ha hb
    exact z_vertices_far_light hw hconn hab ha hb
  have hD_ball : D / (n ^ 2 * 3) = 2 * (11 * δ₀) := by rw [hD_eq, hδ₀_def]; ring
  have hD_sep : D / (n ^ 2 * 33) = 2 * δ₀ := by rw [hD_eq, hδ₀_def]; ring
  have hZ_far_heavy : ∀ a ∈ Z, ∀ b ∈ Z, a ≠ b →
      D / (n ^ 2 * 33) < @dist V pms.toDist a b := by
    intro a ha b hb hab
    rw [hD_sep, show @dist V pms.toDist a b =
      2 * @dist V (vwspPMSLight G w hw hconn).toDist a b from
      vwspPMS_dist_eq_two_vwspPMSLight_dist G w hw hconn a b]
    linarith [hZ_far a ha b hb hab]
  -- Z-large/small threshold
  set k := ⌈(13 : ℝ) / (40 * ↑h) * n⌉₊ with hk_def
  by_cases hZ_large : 2 * k ≤ Z.card
  · -- Z-LARGE CASE
    obtain ⟨A, B, hAS, hBS, hABdisj, hAk, hBk, hABfar⟩ :=
      split_far_finset_into_halves hZ_large
        (fun a ha b hb hab => hZ_far_heavy a ha b hb hab)
    refine Or.inr (Or.inl ⟨A, B, ?_, ?_, ?_⟩)
    · have : (13 : ℝ) / (40 * ↑h) * n ≤ ↑k := Nat.le_ceil _
      linarith [show (k : ℝ) ≤ A.card from by exact_mod_cast hAk]
    · have : (13 : ℝ) / (40 * ↑h) * n ≤ ↑k := Nat.le_ceil _
      linarith [show (k : ℝ) ≤ B.card from by exact_mod_cast hBk]
    · intro b hb
      have hA_nonempty : (A : Set V).Nonempty := by
        have : 0 < k := by rw [hk_def]; apply Nat.ceil_pos.mpr; positivity
        exact Finset.coe_nonempty.mpr (Finset.card_pos.mp (by omega))
      rw [Metric.le_infDist hA_nonempty]
      intro a ha
      have := hABfar a (Finset.mem_coe.mp ha) b hb
      linarith [dist_comm b a]
  · -- Z-SMALL CASE
    push_neg at hZ_large
    set S : Set V := {v | w v ≤ δ₀} with hS_def
    set G' := G.comap (Subtype.val : S → V) with hG'_def
    haveI : DecidableEq V := Classical.decEq V
    -- Z.card ≤ Fintype.card V
    have hZ_le_n : Z.card ≤ Fintype.card V := Finset.card_filter_le _ _
    -- |S| = n - |Z|
    have hS_card : Fintype.card S = Fintype.card V - Z.card := by
      rw [ Fintype.card_ofFinset ];
      rw [ ← Finset.card_compl, Finset.compl_filter ];
      simp +decide [ hS_def ];
      congr
    -- |S| > 0
    have hZ_lt_n : Z.card < Fintype.card V := by
      refine' lt_of_lt_of_le hZ_large _;
      rw [ ← @Nat.cast_le ℝ ] ; push_cast ; nlinarith [ Nat.ceil_lt_add_one ( show 0 ≤ ( 13 : ℝ ) / ( 40 * h ) * n by positivity ), show ( h : ℝ ) ≥ 2 by norm_cast, mul_div_cancel₀ ( 13 : ℝ ) ( by positivity : ( 40 * h : ℝ ) ≠ 0 ) ]
    have hS_pos : 0 < Fintype.card S := by rw [hS_card]; omega
    -- |S| ≥ n - 2k + 1
    have hnS_lower : (Fintype.card V : ℝ) - 2 * ↑k + 1 ≤ ↑(Fintype.card S) := by
      rw [ hS_card, Nat.cast_sub ( by linarith ) ] ; linarith [ show ( Z.card : ℝ ) + 1 ≤ 2 * k from mod_cast hZ_large ] ;
    -- Define shared parameters (used by both connected and disconnected cases)
    set m := h * (h - 1) / 2 with hm_def
    have hm_pos : 1 ≤ m := by
      simp only [hm_def]
      have : 2 ≤ h * (h - 1) := by nlinarith [Nat.one_le_iff_ne_zero.mpr (by omega : h - 1 ≠ 0)]
      omega
    have hm_edges : (completeGraph (Fin h)).edgeSet.ncard = m :=
      completeGraph_edgeSet_ncard h
    set nS := Fintype.card S with hnS_def
    set N := Fintype.card V with hN_def
    set ε' := (13 : ℝ) / (40 * ↑h) * ↑N / ↑nS with hε'_def
    set η' := (1 : ℝ) / (32 * (↑h : ℝ) ^ 2) * ↑N / ↑nS with hη'_def
    have hε'_nonneg : 0 ≤ ε' := by positivity
    have hη'_nonneg : 0 ≤ η' := by positivity
    have hparam : 2 * (↑h : ℝ) * ε' + ((↑h : ℝ) + ↑m - 1) * η' < 1 := by
      convert z_small_param_condition h hh N nS hS_pos hnlarge hnS_lower using 1;
      rw [ Nat.cast_div ] <;> norm_num;
      · rw [ Nat.cast_sub ( by linarith ) ] ; ring;
      · exact even_iff_two_dvd.mp ( Nat.even_mul_pred_self _ )
    set μS : FinOuterMeasure S := {
      toFun := fun X => (X.toFinset.card : ℝ) / (↑nS : ℝ)
      empty := by simp
      mono := fun {X Y} hXY => by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast Finset.card_le_card (Set.toFinset_mono hXY)
      union_le := fun X Y => by
        simp only [Set.toFinset_union]
        calc (↑(X.toFinset ∪ Y.toFinset).card : ℝ) / ↑nS
            ≤ (↑X.toFinset.card + ↑Y.toFinset.card) / ↑nS := by
              apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ ↑nS)
              exact_mod_cast Finset.card_union_le _ _
          _ = _ := by ring
    } with hμS_def
    have hμS_univ : μS Set.univ = 1 := by
      convert countingFinOuterMeasure_univ hS_pos using 1
    by_cases hconn' : G'.Connected
    · -- CONNECTED G[S] CASE: apply pure_pairs_fat_model to G[S]
      set hw' : ∀ v : S, 0 ≤ (w ∘ Subtype.val) v := fun v => hw v.val with hw'_def
      letI pmsS : PseudoMetricSpace S :=
        vwspPMSLight (SimpleGraph.comap Subtype.val G) (w ∘ Subtype.val) hw' hconn'
      have hball := @vwsp_hG_ball S _ _ (SimpleGraph.comap Subtype.val G)
        (inferInstance) (w ∘ Subtype.val) hw' hconn' δ₀ hδ₀_nonneg
      have hpath := @vwsp_hG_path S _ _ (SimpleGraph.comap Subtype.val G)
        (inferInstance) (w ∘ Subtype.val) hw' hconn' δ₀ hδ₀_nonneg
      -- Apply pure_pairs_fat_model
      have result := @pure_pairs_fat_model S _ pmsS
        (SimpleGraph.comap Subtype.val G) h m hm_pos
        ε' η' hε'_nonneg hη'_nonneg hparam
        μS hμS_univ (completeGraph (Fin h)) hm_edges
        δ₀ hδ₀_nonneg hball hpath
      rcases result with ⟨x, hx_ball⟩ | ⟨AS, BS, hAS, hBS, hAB⟩ | hfat
      · -- Outcome 1: Dense ball → convert to dense ball in G
        left
        use x.val, (setBall {x} (11 * δ₀)).toFinset.image Subtype.val;
        refine' ⟨ _, _, _ ⟩;
        · simp +decide [ setBall ];
          exact hδ₀_nonneg;
        · simp +decide [ setBall ];
          intro s hs hdist
          have hdist_light : @dist V (vwspPMSLight G w hw hconn).toDist x.val s ≤ 11 * δ₀ := by
            convert vwsp_dist_subgraph_ge hw hconn hconn' x ⟨ s, hs ⟩ |> le_trans <| hdist using 1;
          linarith [ vwspPMS_dist_eq_two_vwspPMSLight_dist G w hw hconn x.val s ];
        · rw [ Finset.card_image_of_injective _ Subtype.coe_injective ];
          contrapose! hx_ball;
          convert div_le_div_of_nonneg_right hx_ball.le ( Nat.cast_nonneg nS ) using 1
      · -- Outcome 2: Well-separated pair → convert to pair in G
        right; left
        -- AS BS : Set S, hAS : ε' < μS AS, hBS : ε' < μS BS
        -- hAB : ∀ a ∈ AS, ∀ b ∈ BS, δ₀ < dist a b (in pmsS = vwspPMSLight G[S])
        use AS.toFinset.image Subtype.val, BS.toFinset.image Subtype.val
        have hnS_pos_r : (0 : ℝ) < ↑nS := Nat.cast_pos.mpr hS_pos
        refine ⟨?_, ?_, ?_⟩
        · -- |A| ≥ 13/(40h) * n
          rw [Finset.card_image_of_injective _ Subtype.val_injective]
          have hAS' : ε' < ↑AS.toFinset.card / ↑nS := hAS
          rw [hε'_def] at hAS'
          rw [div_lt_div_iff_of_pos_right hnS_pos_r] at hAS'
          linarith
        · -- |B| ≥ 13/(40h) * n
          rw [Finset.card_image_of_injective _ Subtype.val_injective]
          have hBS' : ε' < ↑BS.toFinset.card / ↑nS := hBS
          rw [hε'_def] at hBS'
          rw [div_lt_div_iff_of_pos_right hnS_pos_r] at hBS'
          linarith
        · -- infDist condition
          intro b hb
          simp only [Finset.mem_image] at hb
          obtain ⟨b', hb'mem, rfl⟩ := hb
          rw [hD_sep]
          have hA_nonempty : (↑(AS.toFinset.image Subtype.val) : Set V).Nonempty := by
            rw [Finset.coe_nonempty, Finset.image_nonempty, Set.toFinset_nonempty]
            by_contra hemp; push_neg at hemp
            have : μS.toFun AS = 0 := by rw [hemp]; exact μS.empty
            linarith [hε'_nonneg]
          rw [Metric.le_infDist hA_nonempty]
          intro a ha
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Set.mem_toFinset] at ha
          obtain ⟨a', ha'mem, rfl⟩ := ha
          have hfar_light : δ₀ < G.weightedDistLight w a'.val b'.val := by
            apply vwsp_light_dist_gt_of_restrict_gt hw hconn hδ₀_nonneg
              (fun v hv => hv) (fun v hv => hv) hconn'
            exact hAB a' ha'mem b' (Set.mem_toFinset.mp hb'mem)
          have h1 : @dist V pms.toDist b'.val a'.val =
              2 * G.weightedDistLight w b'.val a'.val := by
            show G.weightedDist w b'.val a'.val = 2 * G.weightedDistLight w b'.val a'.val
            rw [weightedDistLight_eq_half]; ring
          have h2 : G.weightedDistLight w b'.val a'.val =
              G.weightedDistLight w a'.val b'.val := by
            simp only [weightedDistLight_eq_half]
            rw [weightedDist_symm]
          linarith
      · -- Outcome 3: Fat model → induced minor in G
        right; right
        exact z_small_fat_model_convert _ _ _ ( fatModel_to_hasInducedMinor_internal hδ₀_nonneg ( fun x y hxy => by
          convert comap_adj_dist_le hw ( fun v hv => hv ) hconn' x y hxy using 1 ) hfat.some )
    · -- DISCONNECTED G[S] CASE
      -- When G[S] is disconnected, the paper's approach requires an extended metric
      -- (allowing ∞ for cross-component distances). Since Lean's PseudoMetricSpace
      -- requires finite distances, we handle this case by producing a well-separated
      -- pair or induced minor directly.
      --
      -- Key insight: vertices in different G[S]-components have G-light distance > δ₀,
      -- hence dist_heavy > 2δ₀ = D/(n²·33). So any partition of S into
      -- component-unions gives a well-separated pair.
      --
      -- The challenge is ensuring both sides have size ≥ 13n/(40h).
      -- When no single component dominates, a greedy partition works.
      -- When one component dominates, we apply pure_pairs_fat_model to it.
      -- Use disconnected metric
      have hS_mem : ∀ v ∈ S, w v ≤ δ₀ := fun v hv => hv
      have hS_comp : ∀ v, w v ≤ δ₀ → v ∈ S := fun v hv => hv
      have hS_card12 : 12 ≤ Fintype.card S := by
        refine' le_trans _ ( show Fintype.card S ≥ N - 2 * k from _ );
        · refine' Nat.le_sub_of_add_le' _;
          refine' Nat.le_of_lt_succ _;
          rw [ ← @Nat.cast_lt ℝ ] ; norm_num;
          refine' lt_of_le_of_lt ( add_le_add ( mul_le_mul_of_nonneg_left ( Nat.ceil_lt_add_one ( by positivity ) |> le_of_lt ) zero_le_two ) le_rfl ) _;
          field_simp;
          nlinarith only [ hnlarge, show ( h : ℝ ) ≥ 2 by norm_cast ];
        · exact Nat.sub_le_of_le_add <| by rw [ ← @Nat.cast_le ℝ ] ; push_cast; linarith;
      set Md := (Fintype.card S : ℝ) * δ₀ + 1
      have hMd_bound : (Fintype.card S : ℝ) * δ₀ ≤ Md := le_add_of_nonneg_right zero_le_one
      have hMd_pos : δ₀ < Md := by nlinarith [show (1 : ℝ) ≤ Fintype.card S by exact_mod_cast hS_pos]
      have hMd_pos5 : 5 * δ₀ < Md := by nlinarith [show (12 : ℝ) ≤ Fintype.card S by exact_mod_cast hS_card12]
      letI pmsD := disconnPMS G S w hw δ₀ hδ₀_nonneg hS_mem Md hMd_bound
      have hball := disconn_hG_ball hw hconn hδ₀_nonneg hS_mem hS_comp hMd_bound hMd_pos
      have hpath := disconn_hG_path hw hconn hδ₀_nonneg hS_mem hS_comp hMd_bound hMd_pos5
      have result := @pure_pairs_fat_model S _ pmsD
        (SimpleGraph.comap Subtype.val G) h m hm_pos ε' η' hε'_nonneg hη'_nonneg hparam
        μS hμS_univ (completeGraph (Fin h)) hm_edges δ₀ hδ₀_nonneg hball hpath
      rcases result with ⟨xb, hxb⟩ | ⟨AS, BS, hAS, hBS, hAB⟩ | hfat
      · -- Ball outcome: same as connected case but with disconnected metric
        left
        use xb.val, (setBall {xb} (11 * δ₀)).toFinset.image Subtype.val
        refine' ⟨ _, _, _ ⟩
        · simp +decide [setBall, disconnDist_self hw]
          linarith [mul_nonneg (show (0:ℝ) ≤ 11 from by norm_num) hδ₀_nonneg]
        · simp +decide [setBall]
          intro s hs hdist_s
          have h11_lt_Md : 11 * δ₀ < Md := by nlinarith [show (12 : ℝ) ≤ Fintype.card S by exact_mod_cast hS_card12]
          have hreach : (G.comap (Subtype.val : S → V)).Reachable xb ⟨s, hs⟩ :=
            reachable_of_disconnDist_le h11_lt_Md hdist_s
          have hdist_light : @dist V (vwspPMSLight G w hw hconn).toDist xb.val s ≤ 11 * δ₀ :=
            le_trans (disconnDist_ge_G_light hw hconn (by linarith) hreach) hdist_s
          linarith [vwspPMS_dist_eq_two_vwspPMSLight_dist G w hw hconn xb.val s]
        · rw [Finset.card_image_of_injective _ Subtype.coe_injective]
          contrapose! hxb
          convert div_le_div_of_nonneg_right hxb.le (Nat.cast_nonneg nS) using 1
      · -- Well-separated pair outcome
        right; left
        use AS.toFinset.image Subtype.val, BS.toFinset.image Subtype.val
        have hnS_pos_r : (0 : ℝ) < ↑nS := Nat.cast_pos.mpr hS_pos
        refine ⟨?_, ?_, ?_⟩
        · rw [Finset.card_image_of_injective _ Subtype.val_injective]
          have hAS' : ε' < ↑AS.toFinset.card / ↑nS := hAS
          rw [hε'_def] at hAS'
          rw [div_lt_div_iff_of_pos_right hnS_pos_r] at hAS'
          linarith
        · rw [Finset.card_image_of_injective _ Subtype.val_injective]
          have hBS' : ε' < ↑BS.toFinset.card / ↑nS := hBS
          rw [hε'_def] at hBS'
          rw [div_lt_div_iff_of_pos_right hnS_pos_r] at hBS'
          linarith
        · intro b hb
          simp only [Finset.mem_image] at hb
          obtain ⟨b', hb'mem, rfl⟩ := hb
          rw [hD_sep]
          have hA_nonempty : (↑(AS.toFinset.image Subtype.val) : Set V).Nonempty := by
            rw [Finset.coe_nonempty, Finset.image_nonempty, Set.toFinset_nonempty]
            by_contra hemp; push_neg at hemp
            have : μS.toFun AS = 0 := by rw [hemp]; exact μS.empty
            linarith [hε'_nonneg]
          rw [Metric.le_infDist hA_nonempty]
          intro a ha
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Set.mem_toFinset] at ha
          obtain ⟨a', ha'mem, rfl⟩ := ha
          have hfar_disconn : δ₀ < disconnDist G S w Md a' b' := by
            have := hAB a' ha'mem b' (Set.mem_toFinset.mp hb'mem)
            rwa [disconnPMS_dist_eq hw hδ₀_nonneg hS_mem hMd_bound] at this
          have hfar_light : δ₀ < G.weightedDistLight w a'.val b'.val :=
            disconnDist_gt_implies_G_light_gt hw hconn hδ₀_nonneg hS_mem hS_comp hMd_pos hfar_disconn
          have h1 : @dist V pms.toDist b'.val a'.val =
              2 * G.weightedDistLight w b'.val a'.val := by
            show G.weightedDist w b'.val a'.val = 2 * G.weightedDistLight w b'.val a'.val
            rw [weightedDistLight_eq_half]; ring
          have h2 : G.weightedDistLight w b'.val a'.val =
              G.weightedDistLight w a'.val b'.val := by
            simp only [weightedDistLight_eq_half]
            rw [weightedDist_symm]
          linarith
      · -- Fat model outcome
        right; right
        exact z_small_fat_model_convert _ _ _
          (fatModel_to_hasInducedMinor_internal hδ₀_nonneg
            (fun x y hxy => by
              show disconnDist G S w Md x y ≤ δ₀
              exact disconn_adj_dist_le hw hS_mem hxy)
            hfat.some)

/-! ## Main theorem -/

theorem pure_pairs_dichotomy
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ℕ) (hh : 2 ≤ h) (hconn : G.Connected)
    (hIMF : ¬G.ContainsInducedMinor (oneSubdivision h))
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hn : 0 < Fintype.card V) :
    let pms := vwspPMS G w hw hconn
    let n := (Fintype.card V : ℝ)
    let D := @pairDistSum V _ pms
    (∃ (x₀ : V) (S : Finset V), x₀ ∈ S ∧
      (∀ s ∈ S, @dist V pms.toDist x₀ s ≤ D / (n ^ 2 * 3)) ∧
      (1 : ℝ) / (32 * (h : ℝ) ^ 2) * n ≤ S.card) ∨
    (∃ (A B : Finset V),
      (13 : ℝ) / (40 * (h : ℝ)) * n ≤ A.card ∧
      (13 : ℝ) / (40 * (h : ℝ)) * n ≤ B.card ∧
      ∀ b ∈ B, D / (n ^ 2 * 33) ≤
        @Metric.infDist V pms b (↑A : Set V)) := by
  by_cases hsmall : (Fintype.card V : ℝ) ≤ 32 * (h : ℝ) ^ 2
  · exact Or.inl (pure_pairs_dichotomy_small_n G h hh hconn w hw hn hsmall)
  push_neg at hsmall
  by_cases hD : @pairDistSum V _ (vwspPMS G w hw hconn) = 0
  · exact Or.inl (pure_pairs_dichotomy_D_zero G h hh hconn w hw hn hD)
  push_neg at hD
  have trichotomy := pure_pairs_vwsp_dichotomy G h hh hconn w hw hn hsmall
  rcases trichotomy with h1 | h2 | hIM
  · exact Or.inl h1
  · exact Or.inr h2
  · exfalso; exact hIMF (hasInducedMinor_graphOneSubdiv_to_oneSubdivision G h hIM)

end
