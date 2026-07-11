/-
# Proof of the Main Separator Theorem

This file contains the full proof of the main separator theorem, including:
* `induced_minor_free_hereditary` — heredity of induced-minor-freeness
* `edgeFinset_card_induce_le` — edge count monotonicity under induced subgraphs
* `kl_dual_bound` — QDual(G) ≥ n²/(64h√m) from the KL congestion bound
* `kl_induced_minor_bound` — Q(G) ≥ n²/(64h√m) via LP strong duality
* `coarse_pure_pairs_bound` — Q ≤ 625h²·Q̄
* `main_separator_theorem_proof` — the main theorem

For the statement-level definitions (balanced separators, induced minors,
oneSubdivision), see `Defs.lean`. For proof-level definitions (Qbar, Qspread,
QDual), see `ProofDefs.lean`.
-/
import Mathlib
import InducedMinorFreeSeparators.ProofDefs
import InducedMinorFreeSeparators.Duality
import InducedMinorFreeSeparators.Separator
import InducedMinorFreeSeparators.EmbeddingTheorem
import InducedMinorFreeSeparators.CFBridge
import InducedMinorFreeSeparators.RabinovichBound

open Finset BigOperators

/-! ## Heredity of Induced-Minor-Freeness -/

theorem induced_minor_free_hereditary {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (S : Set V)
    (hIMF : ¬G.ContainsInducedMinor H) :
    ¬(G.induce S).ContainsInducedMinor H := by
  by_contra h_contra
  obtain ⟨φ, hφ⟩ := h_contra
  refine' hIMF _
  refine' ⟨ _, _, _, _, _, _ ⟩
  use fun w => Set.image ( fun v : S => v.val ) ( φ w )
  · exact fun w => Set.Nonempty.image _ ( hφ.1 w )
  · intro w
    have := hφ.2.1 w
    convert this.map _
    rotate_left
    exact { v : V // v ∈ ( φ w |> Set.image Subtype.val ) }
    exact SimpleGraph.induce ( ( fun v : S => v.val ) '' φ w ) G
    use fun v => ⟨ v.val, Set.mem_image_of_mem _ v.2 ⟩
    all_goals simp +decide [ Function.Surjective ]
  · exact fun w₁ w₂ h => Set.disjoint_image_of_injective Subtype.coe_injective ( hφ.2.2.1 w₁ w₂ h )
  · intro w₁ w₂ h; rcases hφ.2.2.2.1 w₁ w₂ h with ⟨ v₁, hv₁, v₂, hv₂, h ⟩ ; exact ⟨ _, Set.mem_image_of_mem _ hv₁, _, Set.mem_image_of_mem _ hv₂, h ⟩
  · simp_all +decide [ Set.image ]
    exact hφ.2.2.2.2

/-! ## Edge Count Monotonicity -/

theorem edgeFinset_card_induce_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (G.induce (↑S : Set V)).edgeFinset.card ≤ G.edgeFinset.card := by
  refine' le_trans _ ( Finset.card_le_card _ )
  rotate_left
  exact Finset.image ( fun e : Sym2 { v // v ∈ S } => Sym2.map ( fun v => v.val ) e ) ( ( SimpleGraph.induce ( S : Set V ) G ).edgeFinset )
  · intro e he
    obtain ⟨ e, he, rfl ⟩ := Finset.mem_image.mp he
    rcases e with ⟨ ⟨ u, hu ⟩, ⟨ v, hv ⟩ ⟩ ; aesop
  · rw [ Finset.card_image_of_injective ]
    intro e₁ e₂ h; induction e₁ using Sym2.inductionOn ; induction e₂ using Sym2.inductionOn ; aesop

/-! ## KL Dual Bound -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Korhonen-Lokshtanov dual bound** (derived from `congestion_lower_bound_of_no_induced_minor`).

Every fractional routing on G has max congestion ≥ n²/(64h√m),
where G is K_h^(1)-induced-minor-free. This gives QDual(G) ≥ n²/(64h√m).

Derived by:
1. Specializing the ConcurrentFlow congestion bound to H = oneSubdivision h
2. Bounding 45·√(|W|+|E(H)|) ≤ 64·h
3. Using the bridge QDual_ge_of_cf_bound -/
theorem kl_dual_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (h : ℕ) (hh : 2 ≤ h)
    (hconn : G.Connected)
    (hIMF : ¬G.ContainsInducedMinor (oneSubdivision h))
    (hV : 2 ≤ Fintype.card V) :
    (Fintype.card V : ℝ) ^ 2 /
      (64 * (h : ℝ) * Real.sqrt (G.edgeFinset.card : ℝ)) ≤ QDual G := by
  apply QDual_ge_of_cf_bound hconn
  intro cf
  have hfree : ¬HasInducedMinor G (oneSubdivision h) :=
    fun h_has => hIMF (hasInducedMinor_imp_containsInducedMinor h_has)
  have hcf := congestion_lower_bound_of_no_induced_minor G (oneSubdivision h) cf hfree hV
  have hconst := kl_constant_bound h hh
  by_cases hm : G.edgeFinset.card = 0
  · have h0 : Real.sqrt (↑G.edgeFinset.card : ℝ) = 0 := by simp [hm]
    simp only [h0, mul_zero, div_zero] at hcf ⊢
    linarith
  · have hm_pos : (0 : ℝ) < G.edgeFinset.card := by exact_mod_cast Nat.pos_of_ne_zero hm
    calc (Fintype.card V : ℝ) ^ 2 / (64 * (h : ℝ) * Real.sqrt (G.edgeFinset.card : ℝ))
        ≤ (Fintype.card V : ℝ) ^ 2 /
          (45 * Real.sqrt ((Fintype.card (SubdivVertex h) : ℝ) +
            ↑((oneSubdivision h).edgeFinset.card)) *
          Real.sqrt (G.edgeFinset.card : ℝ)) := by
          apply div_le_div_of_nonneg_left (by positivity)
            (by apply mul_pos; apply mul_pos; norm_num
                exact Real.sqrt_pos.mpr (by
                  haveI : Nonempty (SubdivVertex h) := ⟨.inl ⟨0, by omega⟩⟩
                  have : 0 < Fintype.card (SubdivVertex h) := Fintype.card_pos
                  positivity)
                exact Real.sqrt_pos.mpr hm_pos)
          exact mul_le_mul_of_nonneg_right hconst (Real.sqrt_nonneg _)
      _ < cf.congestion := hcf

/-! ## Derived Results -/

/-- **KL bound on Q**, derived from LP strong duality + KL dual bound. -/
theorem kl_induced_minor_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ℕ) (hh : 2 ≤ h)
    (hconn : G.Connected)
    (hIMF : ¬G.ContainsInducedMinor (oneSubdivision h))
    (hV : 2 ≤ Fintype.card V) :
    (Fintype.card V : ℝ) ^ 2 /
      (64 * (h : ℝ) * Real.sqrt (G.edgeFinset.card : ℝ)) ≤ Qspread G := by
  haveI : Nonempty V := hconn.nonempty
  rw [lp_strong_duality G hconn]
  exact kl_dual_bound G h hh hconn hIMF hV

omit [DecidableEq V] in
/-- **Coarse Pure Pairs + Embedding bound** -/
theorem coarse_pure_pairs_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ℕ) (hh : 2 ≤ h)
    (hconn : G.Connected)
    (hIMF : ¬G.ContainsInducedMinor (oneSubdivision h)) :
    Qspread G ≤ 625 * (h : ℝ) ^ 2 * Qbar G :=
  coarse_pure_pairs_bound_derived G h hh hconn hIMF

/-! ## Separator from Expansion -/

theorem embed_to_sep_v2 (G : SimpleGraph V) (β : ℝ) (hβ : 0 < β)
    (hn : 2 ≤ Fintype.card V)
    (hQbar : ∀ (S : Finset V), 2 ≤ S.card → S.Nonempty →
      (G.induce (↑S : Set V)).Connected →
      ((S.card : ℝ)^2 / β ≤ Qbar (G.induce (↑S : Set V)))) :
    G.HasBalancedSeparator (2/3) (4 * β) := by
  apply expansion_to_sep
  · positivity
  · exact hn
  · intro W hW
    by_cases hconn : (G.induce (W : Set V)).Connected
    · apply connected_qbar_has_expansion_pair G W hW hconn β hβ (hQbar W hW (Finset.card_pos.mp (by linarith)) hconn)
    · exact disconnected_has_expansion_pair G W hW hconn ( 4 * β ) ( by positivity )

/-! ## Main Theorem (proof) -/

omit [DecidableEq V] in
private lemma card_ge_two_of_edge {G : SimpleGraph V} [DecidableRel G.Adj]
    (hm : 1 ≤ G.edgeFinset.card) : 2 ≤ Fintype.card V := by
  contrapose! hm
  interval_cases _ : Fintype.card V
  · simp_all +decide [ Fintype.card_eq_zero_iff ]
    exact Subsingleton.elim _ _
  · rw [ Fintype.card_eq_one_iff ] at * ; aesop

/-- The flow lower bound on `Qspread` for every connected induced subgraph,
shared by both branches of the main theorem. -/
private lemma kl_spread_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ℕ) (hh : 2 ≤ h)
    (hIMF : ¬G.ContainsInducedMinor (oneSubdivision h))
    (S : Finset V) (hS : 2 ≤ S.card) (hS_connected : (G.induce (↑S : Set V)).Connected) :
    Qspread (G.induce (↑S : Set V)) ≥
      (S.card : ℝ) ^ 2 / (64 * h * Real.sqrt (G.edgeFinset.card : ℝ)) := by
  have hS_card : 2 ≤ Fintype.card { v // v ∈ (↑S : Set V) } := by
    rw [show Fintype.card { v // v ∈ (↑S : Set V) } = S.card from Fintype.card_coe S]
    exact hS
  refine' le_trans _ ( kl_induced_minor_bound _ _ _ hS_connected _ hS_card)
  any_goals assumption
  · gcongr
    · refine' mul_pos ( mul_pos ( by norm_num ) ( Nat.cast_pos.mpr ( by linarith ) ) ) ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr _ ) )
      contrapose! hS; simp_all +decide [ SimpleGraph.connected_iff_exists_forall_reachable ]
      exact lt_of_le_of_lt ( Finset.card_le_one.mpr fun x hx y hy => by obtain ⟨ a, ha, ha' ⟩ := hS_connected; have := ha' x hx; have := ha' y hy; aesop ) ( by decide )
    · simp +decide [ Fintype.card_subtype ]
    · convert edgeFinset_card_induce_le G S using 1
  · exact induced_minor_free_hereditary _ _ _ hIMF

/-- **Separator from an abstract distortion (spread) bound.** If every connected
induced subgraph satisfies `Qspread ≤ ρ · Qbar`, then `G` has a `(2/3)`-balanced
separator of size `≤ 4 · (64 h √m · ρ)`. -/
theorem separator_of_spread_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ℕ) (hh : 2 ≤ h)
    (hm : 1 ≤ G.edgeFinset.card)
    (hIMF : ¬G.ContainsInducedMinor (oneSubdivision h))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hbound : ∀ (S : Finset V), 2 ≤ S.card → S.Nonempty →
        (G.induce (↑S : Set V)).Connected →
        Qspread (G.induce (↑S : Set V)) ≤ ρ * Qbar (G.induce (↑S : Set V))) :
    G.HasBalancedSeparator (2/3)
      (4 * (64 * (h : ℝ) * Real.sqrt (G.edgeFinset.card : ℝ) * ρ)) := by
  have hh0 : 0 < (h : ℝ) := by exact_mod_cast (by omega : 0 < h)
  have hm0 : 0 < Real.sqrt (G.edgeFinset.card : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < G.edgeFinset.card))
  apply embed_to_sep_v2 G (64 * (h : ℝ) * Real.sqrt (G.edgeFinset.card : ℝ) * ρ)
    (mul_pos (mul_pos (mul_pos (by norm_num) hh0) hm0) hρ) (card_ge_two_of_edge hm)
  intro S hS hS_nonempty hS_connected
  have hQspread := kl_spread_lower G h hh hIMF S hS hS_connected
  have hQbar : Qspread (G.induce (↑S : Set V)) ≤ ρ * Qbar (G.induce (↑S : Set V)) :=
    hbound S hS hS_nonempty hS_connected
  convert div_le_div_of_nonneg_right hQspread hρ.le |> le_trans <|
    div_le_iff₀' hρ |>.2 hQbar using 1 ; ring

/-- A graph admitting balanced separators of two sizes admits one of size `min`. -/
theorem HasBalancedSeparator.min {G : SimpleGraph V} (c k₁ k₂ : ℝ)
    (h₁ : G.HasBalancedSeparator c k₁) (h₂ : G.HasBalancedSeparator c k₂) :
    G.HasBalancedSeparator c (min k₁ k₂) := by
  rcases le_total k₁ k₂ with hle | hle
  · rw [min_eq_left hle]; exact h₁
  · rw [min_eq_right hle]; exact h₂

omit [DecidableEq V] in
/-- `Qbar` is nonnegative for connected graphs, since the zero solution is feasible. -/
theorem Qbar_nonneg {G : SimpleGraph V} (hconn : G.Connected) : 0 ≤ Qbar G := by
  have : QbarObj (fun _ : V => (0 : ℝ)) ≤ Qbar G :=
    Qbar_le_of_feasible G hconn ⟨fun _ => le_refl _, by simp, by simp⟩
  simpa [QbarObj] using this

theorem main_separator_theorem_proof
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ℕ) (hh : 2 ≤ h)
    (hm : 1 ≤ G.edgeFinset.card)
    (hIMF : ¬G.ContainsInducedMinor (oneSubdivision h)) :
    G.HasBalancedSeparator (2/3)
      (256 * (h : ℝ) * Real.sqrt (G.edgeFinset.card : ℝ) *
        min (1280 * Real.log (Fintype.card V)) (625 * (h : ℝ) ^ 2)) := by
  have hn : 2 ≤ Fintype.card V := card_ge_two_of_edge hm
  have hsep_h : G.HasBalancedSeparator (2/3)
      (4 * (64 * (h : ℝ) * Real.sqrt (G.edgeFinset.card : ℝ) * (625 * (h : ℝ) ^ 2))) :=
    separator_of_spread_bound G h hh hm hIMF (625 * (h : ℝ) ^ 2) (by positivity)
      (fun S _ _ hScon => coarse_pure_pairs_bound (G.induce (↑S : Set V)) h hh hScon
        (induced_minor_free_hereditary _ _ _ hIMF))
  have hlogpos : 0 < Real.log (Fintype.card V) := Real.log_pos (by exact_mod_cast hn)
  have hsep_log : G.HasBalancedSeparator (2/3)
      (4 * (64 * (h : ℝ) * Real.sqrt (G.edgeFinset.card : ℝ) *
        (1280 * Real.log (Fintype.card V)))) := by
    apply separator_of_spread_bound G h hh hm hIMF
      (1280 * Real.log (Fintype.card V)) (by positivity)
    intro S hS _ hScon
    have hScard : 2 ≤ Fintype.card { v // v ∈ (↑S : Set V) } := by
      rw [show Fintype.card { v // v ∈ (↑S : Set V) } = S.card from Fintype.card_coe S]
      exact hS
    have hSle : Fintype.card { v // v ∈ (↑S : Set V) } ≤ Fintype.card V :=
      Fintype.card_subtype_le _
    have hrab := rabinovich_sp_bound (G.induce (↑S : Set V)) hScon hScard
    have hlogmono : Real.log (Fintype.card { v // v ∈ (↑S : Set V) }) ≤
        Real.log (Fintype.card V) :=
      Real.log_le_log
        (by exact_mod_cast (by omega : 0 < Fintype.card { v // v ∈ (↑S : Set V) }))
        (by exact_mod_cast hSle)
    calc Qspread (G.induce (↑S : Set V))
        ≤ 1280 * Real.log (Fintype.card { v // v ∈ (↑S : Set V) }) *
            Qbar (G.induce (↑S : Set V)) := hrab
      _ ≤ 1280 * Real.log (Fintype.card V) * Qbar (G.induce (↑S : Set V)) := by
          apply mul_le_mul_of_nonneg_right _ (Qbar_nonneg hScon)
          nlinarith [hlogmono]
  have hcomb := HasBalancedSeparator.min (2/3) _ _ hsep_log hsep_h
  convert hcomb using 1
  rw [mul_min_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 256 * (h : ℝ) * Real.sqrt (G.edgeFinset.card : ℝ))]
  congr 1 <;> ring
