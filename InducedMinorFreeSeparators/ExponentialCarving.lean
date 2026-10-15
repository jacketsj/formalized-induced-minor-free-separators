/-
# Set-core carving

Metric lemmas used by the logarithmic Rabinovich embedding.  The carving
construction itself is independent of graphs; this file deliberately exposes
that boundary.
-/
import Padding.Embedding.Core
import InducedMinorFreeSeparators.MetricEmbeddings

open Finset BigOperators Metric Set
open PaddedDecomposition

noncomputable section
open Classical

variable {X : Type*} [PseudoMetricSpace X]

/-- Signed distance works unchanged for pseudometrics (the version in the
padding development is stated for metrics). -/
def pseudoSignedDist (A : Set X) (x : X) : ℝ :=
  (Metric.infDist x A - Metric.infDist x Aᶜ) / 2

lemma pseudoSignedDist_nonexpansive (A : Set X) :
    IsNonExpansive (pseudoSignedDist A) := by
  intro x y
  have hA := infDist_nonExpansive A x y
  have hAc := infDist_nonExpansive Aᶜ x y
  simp only [pseudoSignedDist]
  rw [abs_le] at hA hAc ⊢
  constructor <;> linarith [hA.1, hA.2, hAc.1, hAc.2]

lemma pseudoSignedDist_separation {A : Set X} {u v : X} {r : ℝ}
    (hr : 0 ≤ r) (hu : u ∈ A) (hupad : closedBall u r ⊆ A)
    (hv : v ∈ Aᶜ) :
    r / 2 ≤ |pseudoSignedDist A u - pseudoSignedDist A v| := by
  have huA : Metric.infDist u A = 0 := Metric.infDist_zero_of_mem hu
  have hvAc : Metric.infDist v Aᶜ = 0 := Metric.infDist_zero_of_mem hv
  have huAc : r ≤ Metric.infDist u Aᶜ := by
    contrapose! hupad
    rw [Metric.infDist_lt_iff] at hupad
    · exact Set.not_subset.mpr
        ⟨hupad.choose, Metric.mem_closedBall'.mpr hupad.choose_spec.2.le,
          hupad.choose_spec.1⟩
    · exact ⟨v, hv⟩
  have hvA : 0 ≤ Metric.infDist v A := Metric.infDist_nonneg
  simp only [pseudoSignedDist, huA, hvAc]
  rw [abs_of_nonpos] <;> linarith

lemma pseudoSignedDist_compl (A : Set X) (x : X) :
    pseudoSignedDist Aᶜ x = -pseudoSignedDist A x := by
  simp [pseudoSignedDist, compl_compl]
  ring

lemma pseudoSignedDist_abs_compl (A : Set X) (u v : X) :
    |pseudoSignedDist Aᶜ u - pseudoSignedDist Aᶜ v| =
      |pseudoSignedDist A u - pseudoSignedDist A v| := by
  simp only [pseudoSignedDist_compl]
  rw [show -pseudoSignedDist A u - -pseudoSignedDist A v =
      -(pseudoSignedDist A u - pseudoSignedDist A v) by ring, abs_neg]

/-! ## A deterministic thin-annulus lemma -/

/-- The points of `U` at distance at most `t` from a nonempty finite core
`K`. -/
def coreBall (U K : Finset X) (t : ℝ) : Finset X :=
  U.filter fun x => Metric.infDist x (K : Set X) ≤ t

lemma coreBall_mono (U K : Finset X) {s t : ℝ} (hst : s ≤ t) :
    coreBall U K s ⊆ coreBall U K t := by
  intro x hx
  simp only [coreBall, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.trans hst⟩

lemma core_subset_coreBall_zero (U K : Finset X) (hKU : K ⊆ U) :
    K ⊆ coreBall U K 0 := by
  intro x hx
  simp only [coreBall, Finset.mem_filter]
  refine ⟨hKU hx, ?_⟩
  rw [Metric.infDist_zero_of_mem (show x ∈ (K : Set X) from hx)]

/-- Among geometrically spaced radii, one annulus grows by a factor at most
`5/4`.  The integer condition `M * 4^k ≤ 5^k` is the discrete form of
`k = O(log M)`. -/
theorem exists_thin_core_annulus
    (N M k : ℕ) (_hM : 1 ≤ M) (hk : 1 ≤ k)
    (hgrowth : M * 4 ^ k ≤ 5 ^ k)
    (U K : Finset X) (hKU : K ⊆ U) (hKne : K.Nonempty)
    (hcore : U.card < M * K.card)
    (L : ℝ) (hL : 0 ≤ L)
    (hUlarge : N < 2 * U.card)
    (hLsmall : 2 * (coreBall U K L).card ≤ N) :
    let r := L / (2 * (k : ℝ))
    ∃ j : ℕ, j < k ∧
      let I := coreBall U K (2 * (j : ℝ) * r)
      let C := coreBall U K ((2 * (j : ℝ) + 1) * r)
      let O := coreBall U K (2 * ((j + 1 : ℕ) : ℝ) * r)
      I ⊆ C ∧ C ⊆ O ∧ O ⊆ U ∧ K ⊆ I ∧ C.Nonempty ∧
        2 * C.card ≤ N ∧ 4 * (O \ I).card ≤ I.card := by
  dsimp only
  set r : ℝ := L / (2 * (k : ℝ))
  have hr : 0 ≤ r := by positivity
  let B : ℕ → Finset X := fun i => coreBall U K (2 * (i : ℝ) * r)
  have hBmono : Monotone B := by
    intro i j hij
    apply coreBall_mono
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.mul_le_mul_left 2 hij) hr
  have hKB0 : K ⊆ B 0 := by
    simpa [B] using core_subset_coreBall_zero U K hKU
  have hB0 : K.card ≤ (B 0).card := Finset.card_le_card hKB0
  have hrL : 2 * (k : ℝ) * r = L := by
    change 2 * (k : ℝ) * (L / (2 * (k : ℝ))) = L
    field_simp
  have hBk : 2 * (B k).card ≤ N := by
    simpa [B, hrL] using hLsmall
  have hBk_lt : (B k).card < M * (B 0).card := by
    have : (B k).card < U.card := by omega
    exact lt_of_lt_of_le this (le_trans hcore.le (Nat.mul_le_mul_left M hB0))
  have hgood : ∃ j < k, 4 * (B (j + 1)).card ≤ 5 * (B j).card := by
    by_contra! hbad
    have hgrow_iter : ∀ i ≤ k, 5 ^ i * (B 0).card ≤ 4 ^ i * (B i).card := by
      intro i hi
      induction i with
      | zero => simp
      | succ i ih =>
          have hi' : i ≤ k := by omega
          have hik : i < k := by omega
          have hstep : 5 * (B i).card < 4 * (B (i + 1)).card :=
            hbad i hik
          have hstrict : 5 ^ (i + 1) * (B 0).card <
              4 ^ (i + 1) * (B (i + 1)).card := by
            calc
              5 ^ (i + 1) * (B 0).card = (5 ^ i * (B 0).card) * 5 := by ring
              _ ≤ (4 ^ i * (B i).card) * 5 := Nat.mul_le_mul_right 5 (ih hi')
              _ = 4 ^ i * (5 * (B i).card) := by ring
              _ < 4 ^ i * (4 * (B (i + 1)).card) := by
                exact Nat.mul_lt_mul_of_pos_left hstep
                  (show 0 < (4 : ℕ) ^ i by positivity)
              _ = 4 ^ (i + 1) * (B (i + 1)).card := by ring
          exact hstrict.le
    have hchain₁ : 5 ^ k * (B 0).card ≤ 4 ^ k * (B k).card :=
      hgrow_iter k le_rfl
    have hchain₂ : 4 ^ k * (B k).card < 4 ^ k * (M * (B 0).card) :=
      Nat.mul_lt_mul_of_pos_left hBk_lt (show 0 < (4 : ℕ) ^ k by positivity)
    have hchain₃ : 4 ^ k * (M * (B 0).card) ≤ 5 ^ k * (B 0).card := by
      calc
        4 ^ k * (M * (B 0).card) = (M * 4 ^ k) * (B 0).card := by ring
        _ ≤ 5 ^ k * (B 0).card := Nat.mul_le_mul_right _ hgrowth
    omega
  obtain ⟨j, hjk, hj⟩ := hgood
  refine ⟨j, hjk, ?_⟩
  let I := coreBall U K (2 * (j : ℝ) * r)
  let C := coreBall U K ((2 * (j : ℝ) + 1) * r)
  let O := coreBall U K (2 * ((j + 1 : ℕ) : ℝ) * r)
  have hIC : I ⊆ C := coreBall_mono U K (by nlinarith [hr])
  have hCO : C ⊆ O := by
    apply coreBall_mono
    push_cast
    nlinarith
  have hOU : O ⊆ U := Finset.filter_subset _ _
  have hKI : K ⊆ I := by
    intro x hx
    simp only [I, coreBall, Finset.mem_filter]
    refine ⟨hKU hx, ?_⟩
    rw [Metric.infDist_zero_of_mem (show x ∈ (K : Set X) from hx)]
    positivity
  have hCne : C.Nonempty := hKne.mono (hKI.trans hIC)
  have hOL : O ⊆ coreBall U K L := by
    apply coreBall_mono
    rw [← hrL]
    gcongr
    exact_mod_cast Nat.succ_le_iff.mpr hjk
  have hCsmall : 2 * C.card ≤ N :=
    le_trans (Nat.mul_le_mul_left 2 (Finset.card_le_card (hCO.trans hOL))) hLsmall
  have hratio : 4 * O.card ≤ 5 * I.card := by
    simpa [I, O, B, Nat.cast_add, Nat.cast_one, add_mul] using hj
  have hdiff : (O \ I).card + I.card = O.card := by
    rw [Finset.card_sdiff_add_card_eq_card (hIC.trans hCO)]
  refine ⟨hIC, hCO, hOU, hKI, hCne, hCsmall, ?_⟩
  dsimp [I, O, B] at hratio hdiff ⊢
  omega

/-! ## Iterated carving -/

private structure CarvingResult (U : Finset X) (N : ℕ) (r : ℝ) where
  label : X → ℕ
  bad : Finset X
  charge : Finset X
  bad_subset : bad ⊆ U
  charge_subset : charge ⊆ U
  bad_bound : 4 * bad.card ≤ charge.card
  fiber_small : ∀ x ∈ U,
    2 * (U.filter fun y => label y = label x).card ≤ N
  padded : ∀ x ∈ U, x ∉ bad → ∀ y ∈ U, dist x y ≤ r →
    label y = label x

private noncomputable def carving_fuel
    (N M k : ℕ) (hM : 1 ≤ M) (hk : 1 ≤ k)
    (hgrowth : M * 4 ^ k ≤ 5 ^ k)
    (L : ℝ) (hL : 0 ≤ L)
    (cores : ∀ U : Finset X, N < 2 * U.card →
      ∃ K : Finset X, K ⊆ U ∧ K.Nonempty ∧ U.card < M * K.card ∧
        2 * (coreBall U K L).card ≤ N) :
    ∀ (fuel : ℕ) (U : Finset X), U.card ≤ fuel →
      CarvingResult U N (L / (2 * (k : ℝ))) := by
  intro fuel
  induction fuel with
  | zero =>
      intro U hU
      have hU0 : U = ∅ := Finset.card_eq_zero.mp (by omega)
      subst U
      exact {
        label := fun _ => 0
        bad := ∅
        charge := ∅
        bad_subset := Finset.empty_subset _
        charge_subset := Finset.empty_subset _
        bad_bound := by simp
        fiber_small := by simp
        padded := by simp
      }
  | succ fuel ih =>
      intro U hUfuel
      by_cases hactive : N < 2 * U.card
      · let K : Finset X := Classical.choose (cores U hactive)
        have hKspec := Classical.choose_spec (cores U hactive)
        have hKU : K ⊆ U := hKspec.1
        have hKne : K.Nonempty := hKspec.2.1
        have hcore : U.card < M * K.card := hKspec.2.2.1
        have hsmall : 2 * (coreBall U K L).card ≤ N := hKspec.2.2.2
        have hstep := exists_thin_core_annulus N M k hM hk hgrowth U K hKU hKne
          hcore L hL hactive hsmall
        let j : ℕ := Classical.choose hstep
        have hjspec := Classical.choose_spec hstep
        have hjk : j < k := hjspec.1
        let r : ℝ := L / (2 * (k : ℝ))
        let I := coreBall U K (2 * (j : ℝ) * r)
        let C := coreBall U K ((2 * (j : ℝ) + 1) * r)
        let O := coreBall U K (2 * ((j + 1 : ℕ) : ℝ) * r)
        have hIC : I ⊆ C := hjspec.2.1
        have hCO : C ⊆ O := hjspec.2.2.1
        have hOU : O ⊆ U := hjspec.2.2.2.1
        have hKI : K ⊆ I := hjspec.2.2.2.2.1
        have hCne : C.Nonempty := hjspec.2.2.2.2.2.1
        have hCsmall : 2 * C.card ≤ N := hjspec.2.2.2.2.2.2.1
        have hannulus : 4 * (O \ I).card ≤ I.card := hjspec.2.2.2.2.2.2.2
        have hrescard : (U \ C).card ≤ fuel := by
          have hCU : C ⊆ U := hCO.trans hOU
          have hcard := Finset.card_sdiff_of_subset hCU
          have hCpos := hCne.card_pos
          have hlt : (U \ C).card < U.card := by omega
          omega
        let R := ih (U \ C) hrescard
        let lab : X → ℕ := fun x => if x ∈ C then 0 else R.label x + 1
        let bad := (O \ I) ∪ R.bad
        let charge := I ∪ R.charge
        have hRbad : R.bad ⊆ U \ C := R.bad_subset
        have hRcharge : R.charge ⊆ U \ C := R.charge_subset
        have hbadsub : bad ⊆ U := by
          apply Finset.union_subset
          · exact (Finset.sdiff_subset.trans hOU)
          · exact hRbad.trans (Finset.sdiff_subset)
        have hchargesub : charge ⊆ U := by
          apply Finset.union_subset
          · exact hIC.trans (hCO.trans hOU)
          · exact hRcharge.trans Finset.sdiff_subset
        have hcharge_disj : Disjoint I R.charge := by
          apply Finset.disjoint_left.mpr
          intro x hxI hxR
          exact (Finset.mem_sdiff.mp (hRcharge hxR)).2 (hIC hxI)
        have hbadcard : bad.card ≤ (O \ I).card + R.bad.card := by
          exact Finset.card_union_le _ _
        have hchargecard : charge.card = I.card + R.charge.card := by
          rw [Finset.card_union_of_disjoint hcharge_disj]
        have hbadbound : 4 * bad.card ≤ charge.card := by
          rw [hchargecard]
          have hRbound := R.bad_bound
          omega
        refine {
          label := lab
          bad := bad
          charge := charge
          bad_subset := hbadsub
          charge_subset := hchargesub
          bad_bound := hbadbound
          fiber_small := ?_
          padded := ?_
        }
        · intro x hxU
          by_cases hxC : x ∈ C
          · have hfiber : (U.filter fun y => lab y = lab x) = C := by
              ext y
              simp only [Finset.mem_filter]
              constructor
              · rintro ⟨hyU, hylabel⟩
                simp only [lab, if_pos hxC] at hylabel
                by_cases hyC : y ∈ C
                · exact hyC
                · simp [hyC] at hylabel
              · intro hyC
                exact ⟨hOU (hCO hyC), by simp [lab, hxC, hyC]⟩
            rw [hfiber]
            exact hCsmall
          · have hfiber_sub :
                (U.filter fun y => lab y = lab x) ⊆
                  ((U \ C).filter fun y => R.label y = R.label x) := by
              intro y hy
              obtain ⟨hyU, hylab⟩ := Finset.mem_filter.mp hy
              have hyC : y ∉ C := by
                intro hyC
                simp [lab, hxC, hyC] at hylab
              apply Finset.mem_filter.mpr
              refine ⟨Finset.mem_sdiff.mpr ⟨hyU, hyC⟩, ?_⟩
              simpa [lab, hxC, hyC] using hylab
            exact le_trans (Nat.mul_le_mul_left 2 (Finset.card_le_card hfiber_sub))
              (R.fiber_small x (Finset.mem_sdiff.mpr ⟨hxU, hxC⟩))
        · intro x hxU hxbad y hyU hxy
          have hxann : x ∉ O \ I := fun hx => hxbad (Finset.mem_union_left _ hx)
          have hxRbad : x ∉ R.bad := fun hx => hxbad (Finset.mem_union_right _ hx)
          by_cases hxC : x ∈ C
          · have hxI : x ∈ I := by
              by_contra hxI
              exact hxann (Finset.mem_sdiff.mpr ⟨hCO hxC, hxI⟩)
            have hdx : Metric.infDist x (K : Set X) ≤ 2 * (j : ℝ) * r :=
              (Finset.mem_filter.mp hxI).2
            have hdy : Metric.infDist y (K : Set X) ≤ (2 * (j : ℝ) + 1) * r := by
              have hlip := infDist_nonExpansive (K : Set X) y x
              rw [abs_le] at hlip
              nlinarith [dist_comm x y]
            have hyC : y ∈ C := Finset.mem_filter.mpr ⟨hyU, hdy⟩
            simp [lab, hxC, hyC]
          · have hxO : x ∉ O := by
              intro hxO
              exact hxann (Finset.mem_sdiff.mpr ⟨hxO, fun hxI => hxC (hIC hxI)⟩)
            have hyC : y ∉ C := by
              intro hyC
              have hdy : Metric.infDist y (K : Set X) ≤ (2 * (j : ℝ) + 1) * r :=
                (Finset.mem_filter.mp hyC).2
              have hdx : Metric.infDist x (K : Set X) ≤
                  2 * ((j + 1 : ℕ) : ℝ) * r := by
                have hlip := infDist_nonExpansive (K : Set X) x y
                rw [abs_le] at hlip
                push_cast
                nlinarith
              exact hxO (Finset.mem_filter.mpr ⟨hxU, hdx⟩)
            have hrec := R.padded x (Finset.mem_sdiff.mpr ⟨hxU, hxC⟩) hxRbad
              y (Finset.mem_sdiff.mpr ⟨hyU, hyC⟩) hxy
            simpa [lab, hxC, hyC] using congrArg Nat.succ hrec
      · exact {
          label := fun _ => 0
          bad := ∅
          charge := ∅
          bad_subset := Finset.empty_subset _
          charge_subset := Finset.empty_subset _
          bad_bound := by simp
          fiber_small := by
            intro x hx
            simpa using (Nat.le_of_not_gt hactive)
          padded := by simp
        }

variable [Fintype X]

/-- Deterministic set-core carving.  This is the metric content of Lemma 5.1,
with the logarithmic scale encoded by `M * 4^k ≤ 5^k`. -/
theorem core_carving_partition
    (N M k : ℕ) (hN : N = Fintype.card X) (_hN2 : 2 ≤ N)
    (hM : 1 ≤ M) (hk : 1 ≤ k) (hgrowth : M * 4 ^ k ≤ 5 ^ k)
    (L : ℝ) (hL : 0 ≤ L)
    (cores : ∀ U : Finset X, N < 2 * U.card →
      ∃ K : Finset X, K ⊆ U ∧ K.Nonempty ∧ U.card < M * K.card ∧
        2 * (coreBall U K L).card ≤ N) :
    let r := L / (2 * (k : ℝ))
    ∃ P : Partition X,
      (∀ x : X, 2 * (Finset.univ.filter fun y : X => P.label y = P.label x).card ≤ N) ∧
      3 * N ≤ 4 * (Finset.univ.filter fun x : X =>
        closedBall x r ⊆ P.cluster x).card := by
  dsimp only
  let R := carving_fuel N M k hM hk hgrowth L hL cores N Finset.univ
    (by simp [hN])
  let P : Partition X := ⟨R.label⟩
  refine ⟨P, ?_, ?_⟩
  · intro x
    simpa [P] using R.fiber_small x (Finset.mem_univ x)
  · have hbadle : 4 * R.bad.card ≤ N :=
      le_trans R.bad_bound (le_trans (Finset.card_le_card R.charge_subset) (by simp [hN]))
    have hgoodcard :
        (Finset.univ.filter fun x : X => x ∉ R.bad).card = N - R.bad.card := by
      rw [show (Finset.univ.filter fun x : X => x ∉ R.bad) = Finset.univ \ R.bad by
        ext x; simp]
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _)]
      simp [hN]
    have hgoodpad : (Finset.univ.filter fun x : X => x ∉ R.bad) ⊆
        Finset.univ.filter fun x : X => closedBall x (L / (2 * (k : ℝ))) ⊆ P.cluster x := by
      intro x hx
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ x, ?_⟩
      intro y hy
      rw [Partition.mem_cluster_iff]
      exact R.padded x (Finset.mem_univ x) (Finset.mem_filter.mp hx).2 y
        (Finset.mem_univ y) (by simpa [dist_comm] using Metric.mem_closedBall.mp hy)
    have hcardle := Finset.card_le_card hgoodpad
    rw [hgoodcard] at hcardle
    omega

/-- A half-sized partition with at least three quarters of its points padded at
radius `r` has a non-expansive line coordinate with large total separation.

This is the finite random-sign argument of Lemma 6.1.  We use the signed
distance coordinate from `Padding.Embedding.Core`; averaging over all subsets
of the finite set of part labels derandomizes the choice. -/
theorem coordinate_of_half_partition
    (P : Partition X) (r : ℝ) (hr : 0 ≤ r)
    (hn : 2 ≤ Fintype.card X)
    (hhalf : ∀ x : X,
      2 * (Finset.univ.filter fun y : X => P.label y = P.label x).card ≤
        Fintype.card X)
    (hpad : 3 * Fintype.card X ≤ 4 *
      (Finset.univ.filter fun x : X => closedBall x r ⊆ P.cluster x).card) :
    ∃ f : X → ℝ, IsNonExpansive f ∧
      3 * (Fintype.card X : ℝ) ^ 2 * r ≤ 32 * embeddingSum f := by
  let H₀ : Set X := {x | closedBall x r ⊆ P.cluster x}
  let labels : Finset ℕ := Finset.image P.label Finset.univ
  have hlabels : labels.Nonempty := by
    obtain ⟨x⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card X)
    exact ⟨P.label x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩
  have hHcard : 3 * Fintype.card X ≤ 4 * H₀.toFinset.card := by
    simpa [H₀] using hpad
  let score (S : Finset ℕ) : ℝ :=
    ∑ u ∈ H₀.toFinset,
      ∑ v ∈ (Finset.univ.filter fun x => P.label x ∉ S ∧ P.label u ∈ S) ∪
        (Finset.univ.filter fun x => P.label x ∈ S ∧ P.label u ∉ S), r / 2
  have hscore_sum :
      3 * (Fintype.card X : ℝ) ^ 2 * r / 32 *
          2 ^ labels.card ≤
        ∑ S ∈ labels.powerset, score S := by
    have hper : ∀ u ∈ H₀.toFinset,
        (Fintype.card X : ℝ) * r / 8 * 2 ^ labels.card ≤
          ∑ S ∈ labels.powerset,
            ∑ v ∈ (Finset.univ.filter fun x => P.label x ∉ S ∧ P.label u ∈ S) ∪
              (Finset.univ.filter fun x => P.label x ∈ S ∧ P.label u ∉ S), r / 2 := by
      intro u hu
      have havg :
          (∑ S ∈ labels.powerset,
            ∑ v ∈ (Finset.univ.filter fun x => P.label x ∉ S ∧ P.label u ∈ S) ∪
              (Finset.univ.filter fun x => P.label x ∈ S ∧ P.label u ∉ S), r / 2) =
          ∑ v ∈ Finset.univ,
            if P.label v = P.label u then 0
            else (r / 2) * 2 ^ (labels.card - 1) := by
        have hpoint : ∀ v ∈ Finset.univ,
            (∑ S ∈ labels.powerset,
              if (P.label v ≠ P.label u) ∧
                  (P.label v ∈ S ∧ P.label u ∉ S ∨
                   P.label v ∉ S ∧ P.label u ∈ S)
              then r / 2 else 0) =
            if P.label v = P.label u then 0
            else (r / 2) * 2 ^ (labels.card - 1) := by
          intro v hv
          by_cases huv : P.label v = P.label u
          · simp [huv]
          · simp +decide [huv, Finset.sum_ite]
            rw [mul_comm]
            rw [show
              Finset.filter (fun x =>
                P.label v ∈ x ∧ P.label u ∉ x ∨
                P.label v ∉ x ∧ P.label u ∈ x) labels.powerset =
              Finset.biUnion (labels \ {P.label v, P.label u}).powerset
                (fun s => {s ∪ {P.label v}, s ∪ {P.label u}}) from ?_,
              Finset.card_biUnion]
            · rw [Finset.sum_congr rfl fun x hx => Finset.card_pair <| ?_]
              · have hvlabel : P.label v ∈ labels :=
                    Finset.mem_image_of_mem _ (Finset.mem_univ _)
                have hulabel : P.label u ∈ labels :=
                    Finset.mem_image_of_mem _ (Finset.mem_univ _)
                have hpairsub : {P.label v, P.label u} ⊆ labels := by
                  intro x hx
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  rcases hx with rfl | rfl
                  · exact hvlabel
                  · exact hulabel
                have hinter : {P.label v, P.label u} ∩ labels =
                    {P.label v, P.label u} := Finset.inter_eq_left.mpr hpairsub
                rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset,
                  Finset.card_sdiff, hinter, Finset.card_pair huv]
                have hk : 2 ≤ labels.card :=
                  Finset.one_lt_card.2
                    ⟨P.label v, hvlabel, P.label u, hulabel, huv⟩
                rw [show labels.card - 1 = (labels.card - 2) + 1 by omega,
                  pow_succ]
                norm_num
              · simp_all +decide [Finset.ext_iff]
                exact ⟨P.label v, by
                  have := hx
                  have := @this (P.label v)
                  aesop⟩
            · intro s hs t ht hst
              simp_all +decide [Finset.disjoint_left]
              simp_all +decide [Finset.Subset.antisymm_iff,
                Finset.subset_iff, Set.subset_def]
            · ext
              simp [Finset.mem_biUnion, Finset.mem_powerset]
              constructor
              · rintro ⟨h₁, h₂ | h₂⟩
                · use ‹Finset ℕ› \ {P.label v}
                  grind
                · use ‹Finset ℕ› \ {P.label u}
                  grind
              · grind
        rw [← Finset.sum_congr rfl hpoint, Finset.sum_comm]
        simp +decide [Finset.sum_ite]
        congr! 3
        congr! 1
        grind
      rw [havg]
      have houtNat : Fintype.card X ≤
          2 * (Finset.univ.filter fun v : X => P.label v ≠ P.label u).card := by
        have hpart := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset X)) (p := fun v => P.label v = P.label u)
        have hpart' :
            (Finset.univ.filter fun v : X => P.label v = P.label u).card +
              (Finset.univ.filter fun v : X => P.label v ≠ P.label u).card =
              Fintype.card X := by
          simpa only [Finset.card_univ] using hpart
        have hh := hhalf u
        omega
      have hout : (Fintype.card X : ℝ) ≤
          2 * (Finset.univ.filter fun v : X => P.label v ≠ P.label u).card := by
        exact_mod_cast houtNat
      simp only [Finset.sum_ite]
      simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
      have hlabelcard : 1 ≤ labels.card := hlabels.card_pos
      rw [show labels.card = (labels.card - 1) + 1 by omega, pow_succ]
      have hpow : (0 : ℝ) ≤ 2 ^ (labels.card - 1) := by positivity
      have hout' : (Fintype.card X : ℝ) / 2 ≤
          (Finset.univ.filter fun v : X => P.label v ≠ P.label u).card := by linarith
      have hfilter :
          (Finset.univ.filter fun v : X => ¬P.label v = P.label u) =
            Finset.univ.filter fun v : X => P.label v ≠ P.label u := by
        rfl
      rw [hfilter]
      convert mul_le_mul_of_nonneg_right hout'
        (show 0 ≤ r / 2 * 2 ^ (labels.card - 1) by positivity) using 1
      all_goals ring
    rw [Finset.sum_comm]
    have hsum := Finset.sum_le_sum hper
    refine le_trans ?_ hsum
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hr0 : 0 ≤ (Fintype.card X : ℝ) * r / 8 * 2 ^ labels.card := by positivity
    have hcast : (3 : ℝ) * Fintype.card X ≤ 4 * H₀.toFinset.card := by
      exact_mod_cast hHcard
    have hfac : 0 ≤ (Fintype.card X : ℝ) * r / 32 * 2 ^ labels.card := by
      positivity
    convert mul_le_mul_of_nonneg_right hcast hfac using 1 <;> ring
  obtain ⟨S, hSsub, hSscore⟩ : ∃ S ∈ labels.powerset,
      3 * (Fintype.card X : ℝ) ^ 2 * r / 32 ≤ score S := by
    by_contra! hbad
    have hlt : (∑ S ∈ labels.powerset, score S) <
        ∑ _S ∈ labels.powerset,
          (3 * (Fintype.card X : ℝ) ^ 2 * r / 32) :=
      Finset.sum_lt_sum_of_nonempty
        (Finset.powerset_nonempty labels) (fun S hS => hbad S hS)
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset] at hlt
    have hpowcast : (2 : ℝ) ^ labels.card = (2 ^ labels.card : ℕ) := by norm_num
    rw [hpowcast] at hscore_sum
    nlinarith
  let A : Set X := {x | P.label x ∈ S}
  refine ⟨fun x => pseudoSignedDist A x, pseudoSignedDist_nonexpansive A, ?_⟩
  · have hsep : score S ≤ embeddingSum (fun x => pseudoSignedDist A x) := by
      unfold score embeddingSum
      refine le_trans (Finset.sum_le_sum fun u hu => ?_)
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H₀.toFinset)
          (fun _ _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _))
      refine le_trans (Finset.sum_le_sum fun v hv => ?_)
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => abs_nonneg _))
      have hu_pad : closedBall u r ⊆ P.cluster u := by simpa [H₀] using hu
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      rcases hv with ⟨hvS, huS⟩ | ⟨hvS, huS⟩
      · exact pseudoSignedDist_separation hr (show u ∈ A by exact huS)
          (fun z hz => by
            have hzcluster := hu_pad hz
            have : P.label z = P.label u := by simpa [Partition.mem_cluster_iff] using hzcluster
            simpa [A, this] using huS)
          (show v ∈ Aᶜ by simpa [A] using hvS)
      · have hc := pseudoSignedDist_separation (A := Aᶜ) hr
          (show u ∈ Aᶜ by simpa [A] using huS)
          (fun z hz => by
            have hzcluster := hu_pad hz
            have : P.label z = P.label u := by simpa [Partition.mem_cluster_iff] using hzcluster
            simpa [A, this] using huS)
          (show v ∈ (Aᶜ)ᶜ by simpa [A] using hvS)
        rw [pseudoSignedDist_abs_compl] at hc
        simpa using hc
    nlinarith [hSscore, hsep]

end
