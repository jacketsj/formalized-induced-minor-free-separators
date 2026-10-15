/- # Residual-measure structural trichotomy to set-valued cores -/
import InducedMinorFreeSeparators.LogRabinovich

open Finset BigOperators Metric Set
open scoped Classical

noncomputable section

variable {X : Type*} [PseudoMetricSpace X] [Fintype X]

/-- Cardinal form of the structural trichotomy, normalized on an arbitrary
residual set.  This is the exact interface used by exponential carving. -/
def HasResidualTrichotomy (M : ℕ) (δ : ℝ) : Prop :=
  ∀ U : Finset X, Fintype.card X < 2 * U.card →
    (∃ c : X, U.card < M *
      (U.filter fun x => dist c x ≤ 11 * δ).card) ∨
    (∃ A B : Finset X, A ⊆ U ∧ B ⊆ U ∧
      U.card < M * A.card ∧ U.card < M * B.card ∧
      ∀ a ∈ A, ∀ b ∈ B, δ < dist a b)

/-- The two non-minor outcomes of the residual structural trichotomy both
produce a large set-valued core with a half-sized fixed neighborhood. -/
theorem residual_trichotomy_gives_cores
    (M : ℕ) (_hM : 1 ≤ M) (δ : ℝ) (hδ : 0 < δ)
    (htri : HasResidualTrichotomy (X := X) M δ)
    (hsmall : ∀ c : X,
      2 * (Finset.univ.filter fun x : X => dist c x ≤ 12 * δ).card <
        Fintype.card X) :
    ∀ U : Finset X, Fintype.card X < 2 * U.card →
      ∃ K : Finset X, K ⊆ U ∧ K.Nonempty ∧ U.card < M * K.card ∧
        2 * (coreBall U K (δ / 2)).card ≤ Fintype.card X := by
  intro U hU
  rcases htri U hU with hball | hpair
  · obtain ⟨c, hc⟩ := hball
    let K := U.filter fun x => dist c x ≤ 11 * δ
    have hKsub : K ⊆ U := Finset.filter_subset _ _
    have hKne : K.Nonempty := by
      by_contra h
      have hKe : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      change U.card < M * K.card at hc
      rw [hKe] at hc
      simp at hc
    refine ⟨K, hKsub, hKne, hc, ?_⟩
    have hcontain : coreBall U K (δ / 2) ⊆
        Finset.univ.filter fun x : X => dist c x ≤ 12 * δ := by
      intro x hx
      obtain ⟨hxU, hxd⟩ := Finset.mem_filter.mp hx
      obtain ⟨k, hkK, hkdist⟩ := (Set.toFinite (K : Set X)).isCompact
        |>.exists_infDist_eq_dist (by simpa using hKne) x
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ x, ?_⟩
      have hkc : dist c k ≤ 11 * δ := (Finset.mem_filter.mp hkK).2
      rw [hkdist] at hxd
      nlinarith [dist_triangle c k x, dist_comm x k]
    have hcsmall := hsmall c
    exact le_trans (Nat.mul_le_mul_left 2 (Finset.card_le_card hcontain)) hcsmall.le
  · obtain ⟨A, B, hAU, hBU, hAcard, hBcard, hfar⟩ := hpair
    have hAne : A.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h] at hAcard
      simp at hAcard
    have hBne : B.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h] at hBcard
      simp at hBcard
    let NA := coreBall U A (δ / 2)
    let NB := coreBall U B (δ / 2)
    have hdisj : Disjoint NA NB := by
      apply Finset.disjoint_left.mpr
      intro x hxA hxB
      obtain ⟨_, hxda⟩ := Finset.mem_filter.mp hxA
      obtain ⟨_, hxdb⟩ := Finset.mem_filter.mp hxB
      obtain ⟨a, ha, haeq⟩ := (Set.toFinite (A : Set X)).isCompact
        |>.exists_infDist_eq_dist (by simpa using hAne) x
      obtain ⟨b, hb, hbeq⟩ := (Set.toFinite (B : Set X)).isCompact
        |>.exists_infDist_eq_dist (by simpa using hBne) x
      rw [haeq] at hxda
      rw [hbeq] at hxdb
      nlinarith [hfar a ha b hb, dist_triangle a x b, dist_comm a x]
    have hsum : NA.card + NB.card ≤ Fintype.card X := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact le_trans (Finset.card_le_card (Finset.union_subset
        (Finset.filter_subset _ _) (Finset.filter_subset _ _)))
          (by simpa using Finset.card_le_card (Finset.subset_univ U))
    rcases le_total NA.card NB.card with hle | hle
    · refine ⟨A, hAU, hAne, hAcard, ?_⟩
      change 2 * NA.card ≤ Fintype.card X
      omega
    · refine ⟨B, hBU, hBne, hBcard, ?_⟩
      change 2 * NB.card ≤ Fintype.card X
      omega

end
