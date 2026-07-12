/- # Logarithmic Rabinovich embedding from set-valued cores -/
import InducedMinorFreeSeparators.ExponentialCarving

open Finset BigOperators Metric Set
open PaddedDecomposition

noncomputable section
open Classical

variable {X : Type*} [PseudoMetricSpace X] [Fintype X]

/-- Four times the binary ceiling logarithm supplies enough geometric-growth
steps for the `5/4` thin-annulus argument. -/
lemma carving_growth_clog (M : ℕ) :
    M * 4 ^ (4 * Nat.clog 2 M) ≤ 5 ^ (4 * Nat.clog 2 M) := by
  let l := Nat.clog 2 M
  have hM : M ≤ 2 ^ l := Nat.le_pow_clog (by decide) M
  calc
    M * 4 ^ (4 * l) ≤ 2 ^ l * 4 ^ (4 * l) :=
      Nat.mul_le_mul_right _ hM
    _ = 512 ^ l := by
      rw [show 4 * l = 4 * l from rfl, pow_mul]
      norm_num [← mul_pow]
    _ ≤ 625 ^ l := Nat.pow_le_pow_left (by norm_num) _
    _ = 5 ^ (4 * l) := by rw [pow_mul]; norm_num

/-- A coarse real-log bound for the number of deterministic carving scales. -/
lemma four_clog_two_le_log (M : ℕ) (hM : 2 ≤ M) :
    (4 * Nat.clog 2 M : ℝ) ≤ 16 * Real.log (8 * (M : ℝ)) := by
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast hM)
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  have hlogb0 : 0 ≤ Real.logb (2 : ℝ) (M : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ M by omega))
  have hceil := Nat.ceil_lt_add_one hlogb0
  have hceil_eq : ⌈Real.logb (2 : ℝ) (M : ℝ)⌉₊ = Nat.clog 2 M :=
    Real.natCeil_logb_natCast 2 M
  rw [hceil_eq] at hceil
  have hclog : (Nat.clog 2 M : ℝ) < 2 * Real.log (M : ℝ) + 1 := by
    rw [Real.logb] at hceil
    have : Real.log (M : ℝ) / Real.log 2 ≤ 2 * Real.log (M : ℝ) := by
      rw [div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
      nlinarith
    linarith
  have hone : (1 : ℝ) ≤ 2 * Real.log (M : ℝ) := by
    nlinarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ M by exact_mod_cast hM)]
  have hmul : Real.log (M : ℝ) ≤ Real.log (8 * (M : ℝ)) := by
    apply Real.log_le_log (by positivity)
    nlinarith [show (0 : ℝ) ≤ M by positivity]
  nlinarith

/-- The carving and random-sign steps assembled at the Rabinovich scale.  The
only graph-specific input still needed is `hcores`, the large set-valued core
provided by the structural trichotomy. -/
theorem rabinovich_of_core_selection
    (M k : ℕ) (hM : 1 ≤ M) (hk : 1 ≤ k)
    (hgrowth : M * 4 ^ k ≤ 5 ^ k)
    (hn : 2 ≤ Fintype.card X)
    (hcores :
      (∀ x : X, 2 * (Finset.univ.filter fun y : X =>
          dist x y ≤ pairDistSum X /
            (4 * (Fintype.card X : ℝ) ^ 2)).card < Fintype.card X) →
      ∀ U : Finset X, Fintype.card X < 2 * U.card →
        ∃ K : Finset X, K ⊆ U ∧ K.Nonempty ∧ U.card < M * K.card ∧
          2 * (coreBall U K
            (pairDistSum X / (96 * (Fintype.card X : ℝ) ^ 2))).card ≤
              Fintype.card X) :
    ∃ f : X → ℝ, IsNonExpansive f ∧
      pairDistSum X ≤ 2048 * (k : ℝ) * embeddingSum f := by
  by_cases hD : pairDistSum X = 0
  · refine ⟨fun _ => 0, by simp [IsNonExpansive], ?_⟩
    simp [hD, embeddingSum]
  have hDpos : 0 < pairDistSum X := lt_of_le_of_ne
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg)
    (Ne.symm hD)
  by_cases hlarge : ∃ x : X,
      Fintype.card X ≤ 2 * (Finset.univ.filter fun y : X =>
        dist x y ≤ pairDistSum X /
          (4 * (Fintype.card X : ℝ) ^ 2)).card
  · obtain ⟨x, hx⟩ := hlarge
    let S := Finset.univ.filter fun y : X =>
      dist x y ≤ pairDistSum X / (4 * (Fintype.card X : ℝ) ^ 2)
    have hxS : x ∈ S := by
      simp [S]
      positivity
    have hSball : ∀ y ∈ S,
        dist x y ≤ pairDistSum X /
          ((Fintype.card X : ℝ) ^ 2 * 4) := by
      intro y hy
      simpa [S, mul_comm, mul_left_comm] using (Finset.mem_filter.mp hy).2
    have hSsize : (1 / 2 : ℝ) * Fintype.card X ≤ S.card := by
      have hx' : Fintype.card X ≤ 2 * S.card := by
        change Fintype.card X ≤ 2 * S.card
        exact hx
      have hxR : (Fintype.card X : ℝ) ≤ 2 * (S.card : ℝ) := by
        exact_mod_cast hx'
      linarith
    have hcase := large_core_case (X := X) (1 / 2) 4 (by norm_num)
      (by norm_num) (by omega) S x hxS hSball hSsize
    refine ⟨fun z => Metric.infDist z (S : Set X), infDist_nonExpansive _, ?_⟩
    have h8 : pairDistSum X ≤ 8 * embeddingSum
        (fun z => Metric.infDist z (S : Set X)) := by
      norm_num at hcase
      nlinarith
    have hE : 0 ≤ embeddingSum (fun z => Metric.infDist z (S : Set X)) :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    nlinarith [show (1 : ℝ) ≤ k by exact_mod_cast hk]
  · push_neg at hlarge
    let L : ℝ := pairDistSum X / (96 * (Fintype.card X : ℝ) ^ 2)
    have hL : 0 ≤ L := by positivity
    obtain ⟨P, hhalf, hpad⟩ := core_carving_partition
      (X := X) (Fintype.card X) M k rfl hn hM hk hgrowth L hL (hcores hlarge)
    let r : ℝ := L / (2 * (k : ℝ))
    obtain ⟨f, hf, hfsum⟩ := coordinate_of_half_partition P r (by positivity) hn
      hhalf hpad
    refine ⟨f, hf, ?_⟩
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hnpos : (0 : ℝ) < Fintype.card X := by positivity
    have hr_eq : r = pairDistSum X /
        (192 * (Fintype.card X : ℝ) ^ 2 * (k : ℝ)) := by
      dsimp [r, L]
      field_simp
      ring
    rw [hr_eq] at hfsum
    have hden : 0 < 192 * (Fintype.card X : ℝ) ^ 2 * (k : ℝ) := by positivity
    field_simp [ne_of_gt hkpos, ne_of_gt hnpos] at hfsum
    unfold embeddingSum at hfsum ⊢
    nlinarith

/-- Real-log form of `rabinovich_of_core_selection`.  The deterministic
thin-annulus proof loses only a constant factor compared with exponential
sampling. -/
theorem logarithmic_rabinovich_of_core_selection
    (M : ℕ) (hM : 2 ≤ M) (hn : 2 ≤ Fintype.card X)
    (hcores :
      (∀ x : X, 2 * (Finset.univ.filter fun y : X =>
          dist x y ≤ pairDistSum X /
            (4 * (Fintype.card X : ℝ) ^ 2)).card < Fintype.card X) →
      ∀ U : Finset X, Fintype.card X < 2 * U.card →
        ∃ K : Finset X, K ⊆ U ∧ K.Nonempty ∧ U.card < M * K.card ∧
          2 * (coreBall U K
            (pairDistSum X / (96 * (Fintype.card X : ℝ) ^ 2))).card ≤
              Fintype.card X) :
    ∃ f : X → ℝ, IsNonExpansive f ∧
      pairDistSum X ≤ 32768 * Real.log (8 * (M : ℝ)) * embeddingSum f := by
  let k := 4 * Nat.clog 2 M
  have hk : 1 ≤ k := by
    dsimp [k]
    have := Nat.clog_pos (by decide : 1 < 2) (by omega : 1 < M)
    omega
  obtain ⟨f, hf, hsum⟩ := rabinovich_of_core_selection M k (by omega) hk
    (by simpa [k] using carving_growth_clog M) hn hcores
  refine ⟨f, hf, ?_⟩
  have hklog : (k : ℝ) ≤ 16 * Real.log (8 * (M : ℝ)) := by
    simpa [k] using four_clog_two_le_log M hM
  have hE : 0 ≤ embeddingSum f :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  nlinarith

end
