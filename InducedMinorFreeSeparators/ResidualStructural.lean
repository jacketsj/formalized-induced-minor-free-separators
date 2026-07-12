/- # Residual structural trichotomy for vertex-weighted shortest paths -/
import InducedMinorFreeSeparators.ResidualCoreSelection
import InducedMinorFreeSeparators.PurePairsDichotomy

open Set Function CoarsePurePairs SimpleGraph Finset
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Counting outer measure restricted to a fixed finite support. -/
private def restrictedCountingMeasure {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset α) : FinOuterMeasure α where
  toFun A := ((A.toFinset ∩ T).card : ℝ) / T.card
  empty := by simp
  mono := by
    intro A B hAB
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast Finset.card_le_card (by
      intro x hx
      simp only [Finset.mem_inter, Set.mem_toFinset] at hx ⊢
      exact ⟨hAB hx.1, hx.2⟩)
  union_le := by
    intro A B
    simp only [Set.toFinset_union, Finset.union_inter_distrib_right, ← add_div]
    exact div_le_div_of_nonneg_right (by
      exact_mod_cast Finset.card_union_le (A.toFinset ∩ T) (B.toFinset ∩ T))
      (Nat.cast_nonneg _)

/-- Residual-measure version of the structural trichotomy for an arbitrary
positive-edge graph `H` on `Fin h`.  The slightly enlarged denominator
`3h+m+7` provides integral slack for splitting heavy vertices. -/
theorem residual_vwsp_trichotomy
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hconn : G.Connected)
    (h m : ℕ) (hh : 2 ≤ h) (hm : 1 ≤ m)
    (H : SimpleGraph (Fin h)) (hmH : H.edgeSet.ncard = m)
    (hfree : ¬HasInducedMinor_internal G (graphOneSubdiv H))
    (δ : ℝ) (hδ : 0 < δ) :
    letI pms := vwspPMSLight G w hw hconn
    HasResidualTrichotomy (X := V) (3 * h + m + 7) δ := by
  letI pms := vwspPMSLight G w hw hconn
  intro U hUlarge
  set M := 3 * h + m + 7
  have hM : 1 ≤ M := by omega
  have hUne : U.Nonempty := Finset.card_pos.mp (by
    have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hconn.nonempty
    omega)
  by_cases hUsmall : U.card < M
  · let c := hUne.choose
    left
    refine ⟨c, ?_⟩
    have hcU : c ∈ U := hUne.choose_spec
    have hcball : c ∈ U.filter (fun x => dist c x ≤ 11 * δ) := by
      simp [hcU, hδ.le]
    have : 1 ≤ (U.filter fun x => dist c x ≤ 11 * δ).card :=
      Finset.card_pos.mpr ⟨c, hcball⟩
    exact lt_of_lt_of_le hUsmall (Nat.le_mul_of_pos_right M this)
  push_neg at hUsmall
  set t := U.card / M + 1
  have ht : 1 ≤ t := by
    dsimp [t]
    exact Nat.succ_le_succ (Nat.zero_le _)
  have hMt : U.card < M * t := by
    dsimp [t]
    exact Nat.lt_mul_div_succ U.card (by omega : 0 < M)
  set Z := U.filter fun v => δ < w v
  by_cases hZlarge : 2 * t ≤ Z.card
  · obtain ⟨A, B, hAZ, hBZ, _, hAt, hBt, hfar⟩ :=
      split_far_finset_into_halves hZlarge (fun a ha b hb hab =>
        z_vertices_far_light hw hconn hab (Finset.mem_filter.mp ha).2
          (Finset.mem_filter.mp hb).2)
    right
    refine ⟨A, B, hAZ.trans (Finset.filter_subset _ _),
      hBZ.trans (Finset.filter_subset _ _), ?_, ?_, hfar⟩
    · exact lt_of_lt_of_le hMt (Nat.mul_le_mul_left M hAt)
    · exact lt_of_lt_of_le hMt (Nat.mul_le_mul_left M hBt)
  push_neg at hZlarge
  set S : Set V := {v | w v ≤ δ}
  set R := U.filter fun v => w v ≤ δ
  set nR := R.card
  have hpartition : nR + Z.card = U.card := by
    dsimp [nR, R, Z]
    simpa [add_comm] using Finset.card_filter_add_card_filter_not
      (s := U) (p := fun v => w v ≤ δ)
  have hMZ : M * Z.card < 2 * U.card + 2 * M := by
    have htle : M * t ≤ U.card + M := by
      dsimp [t]
      have := Nat.mul_div_le U.card M
      rw [mul_add]
      omega
    calc
      M * Z.card < M * (2 * t) := Nat.mul_lt_mul_of_pos_left hZlarge (by omega)
      _ = 2 * (M * t) := by ring
      _ ≤ 2 * (U.card + M) := Nat.mul_le_mul_left 2 htle
      _ = 2 * U.card + 2 * M := by ring
  have hnRprod : (3 * h + m - 1) * U.card < M * nR := by
    have hUM : M ≤ U.card := hUsmall
    have hpR : (nR : ℝ) + Z.card = U.card := by exact_mod_cast hpartition
    have hzR : (M : ℝ) * Z.card < 2 * U.card + 2 * M := by exact_mod_cast hMZ
    have huR : (M : ℝ) ≤ U.card := by exact_mod_cast hUM
    have hcoef : (3 * h + m - 1 : ℕ) + 8 = M := by dsimp [M]; omega
    rw [← hcoef]
    push_cast
    nlinarith [mul_add (nR : ℝ) (Z.card : ℝ) (M : ℝ)]
  have hnRpos : 0 < nR := by
    by_contra hz
    have hz' : nR = 0 := Nat.eq_zero_of_not_pos hz
    rw [hz', mul_zero] at hnRprod
    omega
  have hS_mem : ∀ v ∈ S, w v ≤ δ := fun v hv => hv
  have hS_comp : ∀ v, w v ≤ δ → v ∈ S := fun v hv => hv
  let T : Finset S := (Set.univ : Set S).toFinset.filter fun x => x.val ∈ U
  have hTcard : T.card = nR := by
    dsimp [T, nR, R, S]
    apply Finset.card_bij (fun x _ => x.val)
    · intro x hx
      simp only [Finset.mem_filter, Set.mem_toFinset, Set.mem_univ, true_and] at hx
      simp [hx, x.2]
    · intro x₁ hx₁ x₂ hx₂ heq
      exact Subtype.ext heq
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      exact ⟨⟨v, hv.2⟩, by simp [hv.1], rfl⟩
  set μS := restrictedCountingMeasure T
  have hμS_univ : μS Set.univ = 1 := by
    dsimp [μS, restrictedCountingMeasure]
    simp only [Set.toFinset_univ, Finset.univ_inter]
    rw [div_self (by exact_mod_cast hTcard.symm ▸ hnRpos.ne')]
  set e : ℝ := (U.card : ℝ) / (M * nR : ℕ)
  have he0 : 0 ≤ e := by positivity
  have hparam : 2 * (h : ℝ) * e + ((h : ℝ) + (m : ℝ) - 1) * e < 1 := by
    have hnRprodR : ((3 * h + m - 1) * U.card : ℕ) < M * nR := hnRprod
    have hnRprodR' : (3 * (h : ℝ) + (m : ℝ) - 1) * U.card < M * nR := by
      have hcast : (((3 * h + m - 1 : ℕ) : ℝ)) =
          3 * (h : ℝ) + (m : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 3 * h + m)]
        push_cast
        ring
      rw [← hcast]
      exact_mod_cast hnRprodR
    dsimp [e]
    push_cast
    have hden : (0 : ℝ) < M * nR := by positivity
    calc
      2 * (h : ℝ) * ((U.card : ℝ) / ((M : ℝ) * nR)) +
          ((h : ℝ) + (m : ℝ) - 1) * ((U.card : ℝ) / ((M : ℝ) * nR)) =
          ((3 * (h : ℝ) + (m : ℝ) - 1) * U.card) / ((M : ℝ) * nR) := by ring
      _ < 1 := (div_lt_one hden).2 hnRprodR'
  have hMdist : (Fintype.card S : ℝ) * δ ≤
      ((Fintype.card S : ℝ) + 12) * δ + 1 := by
    have : (0 : ℝ) ≤ Fintype.card S := by positivity
    nlinarith
  set Md : ℝ := ((Fintype.card S : ℝ) + 12) * δ + 1
  have hMd11 : 11 * δ < Md := by
    dsimp [Md]
    have : (0 : ℝ) ≤ Fintype.card S := by positivity
    nlinarith
  letI pmsD := disconnPMS G S w hw δ hδ.le hS_mem Md hMdist
  have hball := disconn_hG_ball hw hconn hδ.le hS_mem hS_comp hMdist (by linarith : δ < Md)
  have hpath := disconn_hG_path hw hconn hδ.le hS_mem hS_comp hMdist (by linarith : 5 * δ < Md)
  have result := @pure_pairs_fat_model S _ pmsD
    (G.comap (Subtype.val : S → V)) h m hm e e he0 he0 hparam
    μS hμS_univ H hmH δ hδ.le hball hpath
  rcases result with hballout | hpairout | hfat
  · obtain ⟨x, hx⟩ := hballout
    dsimp [μS, restrictedCountingMeasure] at hx
    left
    refine ⟨x.val, ?_⟩
    have hcount : U.card < M *
        ((setBall {x} (11 * δ)).toFinset ∩ T).card := by
      rw [hTcard] at hx
      have hx' : (U.card : ℝ) / ((M : ℝ) * nR) <
          (((setBall {x} (11 * δ)).toFinset ∩ T).card : ℝ) / nR := by
        simpa [e, Nat.cast_mul] using hx
      have hcross := (div_lt_div_iff₀ (by positivity : (0 : ℝ) < (M : ℝ) * nR)
        (by exact_mod_cast hnRpos : (0 : ℝ) < nR)).mp hx'
      have hnRposR : (0 : ℝ) < nR := by exact_mod_cast hnRpos
      have hx'' : (U.card : ℝ) < M *
          ((setBall {x} (11 * δ)).toFinset ∩ T).card := by
        nlinarith
      exact_mod_cast hx''
    refine lt_of_lt_of_le hcount (Nat.mul_le_mul_left M ?_)
    rw [← Finset.card_image_of_injective _ Subtype.val_injective]
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    simp only [Finset.mem_inter, Set.mem_toFinset] at hz
    apply Finset.mem_filter.mpr
    have hzU : z.val ∈ U := by
      have := hz.2
      simp only [T, Finset.mem_filter, Set.mem_toFinset, Set.mem_univ, true_and] at this
      exact this
    refine ⟨hzU, ?_⟩
    obtain ⟨z', hz'x, hdist⟩ := hz.1
    simp only [Set.mem_singleton_iff] at hz'x
    subst z'
    change disconnDist G S w Md x z ≤ 11 * δ at hdist
    have hreach : (G.comap (Subtype.val : S → V)).Reachable x z :=
      reachable_of_disconnDist_le hMd11 hdist
    exact le_trans (disconnDist_ge_G_light hw hconn
      (by positivity : 0 ≤ Md) hreach) hdist
  · obtain ⟨A, B, hA, hB, hAB⟩ := hpairout
    dsimp [μS, restrictedCountingMeasure] at hA hB
    let AU := A.toFinset ∩ T
    let BU := B.toFinset ∩ T
    right
    refine ⟨AU.image Subtype.val, BU.image Subtype.val, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have := (Finset.mem_inter.mp hy).2
      simp only [T, Finset.mem_filter, Set.mem_toFinset, Set.mem_univ, true_and] at this
      exact this
    · intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have := (Finset.mem_inter.mp hy).2
      simp only [T, Finset.mem_filter, Set.mem_toFinset, Set.mem_univ, true_and] at this
      exact this
    · rw [Finset.card_image_of_injective _ Subtype.val_injective]
      rw [hTcard] at hA
      have hA' : (U.card : ℝ) / ((M : ℝ) * nR) <
          (AU.card : ℝ) / nR := by simpa [e, Nat.cast_mul, AU] using hA
      have hcross := (div_lt_div_iff₀ (by positivity : (0 : ℝ) < (M : ℝ) * nR)
        (by exact_mod_cast hnRpos : (0 : ℝ) < nR)).mp hA'
      have hnRposR : (0 : ℝ) < nR := by exact_mod_cast hnRpos
      have : (U.card : ℝ) < M * AU.card := by nlinarith
      exact_mod_cast this
    · rw [Finset.card_image_of_injective _ Subtype.val_injective]
      rw [hTcard] at hB
      have hB' : (U.card : ℝ) / ((M : ℝ) * nR) <
          (BU.card : ℝ) / nR := by simpa [e, Nat.cast_mul, BU] using hB
      have hcross := (div_lt_div_iff₀ (by positivity : (0 : ℝ) < (M : ℝ) * nR)
        (by exact_mod_cast hnRpos : (0 : ℝ) < nR)).mp hB'
      have hnRposR : (0 : ℝ) < nR := by exact_mod_cast hnRpos
      have : (U.card : ℝ) < M * BU.card := by nlinarith
      exact_mod_cast this
    · intro a ha b hb
      simp only [Finset.mem_image] at ha hb
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      have hd := hAB a' (Set.mem_toFinset.mp (Finset.mem_inter.mp ha').1)
        b' (Set.mem_toFinset.mp (Finset.mem_inter.mp hb').1)
      exact disconnDist_gt_implies_G_light_gt hw hconn hδ.le hS_mem hS_comp
        (by linarith : δ < Md) hd
  · exfalso
    apply hfree
    exact hasInducedMinor_internal_of_comap Subtype.val Subtype.val_injective G _
      (fatModel_to_hasInducedMinor_internal hδ.le
        (fun x y hxy => disconn_adj_dist_le hw hS_mem hxy) hfat.some)

end
