import Mathlib

/-!
# Product Independence for Weighted Sums over Pi Types
-/

open Finset Classical
open scoped BigOperators ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {β : ι → Type*} [∀ i, Fintype (β i)]

/-- Rewrite sum over Pi type via Equiv.piEquivPiSubtypeProd -/
lemma sum_pi_decompose (p : ι → Prop) [DecidablePred p]
    (h : (∀ i, β i) → ℝ≥0∞) :
    ∑ f : ∀ i, β i, h f =
    ∑ f_yes : ∀ i : {x // p x}, β ↑i,
      ∑ f_no : ∀ i : {x // ¬p x}, β ↑i,
        h ((Equiv.piEquivPiSubtypeProd p β).symm (f_yes, f_no)) := by
  rw [← Equiv.sum_comp (Equiv.piEquivPiSubtypeProd p β).symm]
  convert Fintype.sum_prod_type
    (fun x => h (Equiv.piEquivPiSubtypeProd p β |>.symm x))

omit [DecidableEq ι] [(i : ι) → Fintype (β i)] in
/-- Product over all i decomposes via piEquivPiSubtypeProd -/
lemma prod_pi_decompose (p : ι → Prop) [DecidablePred p]
    (g : ∀ i, β i → ℝ≥0∞)
    (f_yes : ∀ i : {x // p x}, β ↑i)
    (f_no : ∀ i : {x // ¬p x}, β ↑i) :
    ∏ i, g i ((Equiv.piEquivPiSubtypeProd p β).symm (f_yes, f_no) i) =
    (∏ i : {x // p x}, g ↑i (f_yes i)) *
    (∏ i : {x // ¬p x}, g ↑i (f_no i)) := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ p]
  refine congrArg₂ _
    (Finset.prod_bij (fun x hx => ⟨x, by simpa using hx⟩) ?_ ?_ ?_ ?_)
    (Finset.prod_bij (fun x hx => ⟨x, by simpa using hx⟩) ?_ ?_ ?_ ?_) <;>
    simp +decide [Equiv.piEquivPiSubtypeProd]
  · aesop
  · grind

/-- Sum over subtype Pi of product equals product of sums -/
lemma sum_subtype_pi_prod (p : ι → Prop) [DecidablePred p]
    (g : ∀ i, β i → ℝ≥0∞) :
    ∑ f : ∀ i : {x // p x}, β ↑i, ∏ i : {x // p x}, g ↑i (f i) =
    ∏ i : {x // p x}, ∑ b : β ↑i, g ↑i b := by
  rw [Finset.prod_sum, ← Finset.sum_attach]
  refine Finset.sum_bij (fun f _ => fun i _ => f.val i) ?_ ?_ ?_ ?_ <;>
    simp +decide
  · simp +decide [funext_iff]
  · exact fun b =>
      ⟨fun i => b i (Finset.mem_univ i),
       funext fun i => funext fun _ => rfl⟩

omit [DecidableEq ι] in
/-- If ∑ g_i(b) = 1, then ∏ (∑ g_i(b)) over a subtype = 1 -/
lemma prod_subtype_sum_one (p : ι → Prop) [DecidablePred p]
    (g : ∀ i, β i → ℝ≥0∞) (hg : ∀ i, ∑ b, g i b = 1) :
    ∏ i : {x // p x}, ∑ b : β ↑i, g ↑i b = 1 := by
  aesop

omit [Fintype ι] [DecidableEq ι] [(i : ι) → Fintype (β i)] in
/-- piEquivPiSubtypeProd.symm agrees on p-coordinates regardless of the ¬p component -/
lemma pi_symm_agree_on_yes (p : ι → Prop) [DecidablePred p]
    (f_yes : ∀ i : {x // p x}, β ↑i)
    (f_no f_no' : ∀ i : {x // ¬p x}, β ↑i)
    (i : ι) (hi : p i) :
    (Equiv.piEquivPiSubtypeProd p β).symm (f_yes, f_no) i =
    (Equiv.piEquivPiSubtypeProd p β).symm (f_yes, f_no') i := by
  simp +decide [Equiv.piEquivPiSubtypeProd, hi]

omit [Fintype ι] [DecidableEq ι] [(i : ι) → Fintype (β i)] in
/-- piEquivPiSubtypeProd.symm agrees on ¬p-coordinates regardless of the p component -/
lemma pi_symm_agree_on_no (p : ι → Prop) [DecidablePred p]
    (f_yes f_yes' : ∀ i : {x // p x}, β ↑i)
    (f_no : ∀ i : {x // ¬p x}, β ↑i)
    (i : ι) (hi : ¬p i) :
    (Equiv.piEquivPiSubtypeProd p β).symm (f_yes, f_no) i =
    (Equiv.piEquivPiSubtypeProd p β).symm (f_yes', f_no) i := by
  simp +decide [Equiv.piEquivPiSubtypeProd, hi]

/-
A sum ∑_{(a,b)} h₁(a) * h₂(b) over a product of Fintypes factors.
-/
lemma sum_prod_mul_factor {α₁ α₂ : Type*} [Fintype α₁] [Fintype α₂]
    (h₁ : α₁ → ℝ≥0∞) (h₂ : α₂ → ℝ≥0∞) :
    (∑ a : α₁, ∑ b : α₂, h₁ a * h₂ b) =
    (∑ a : α₁, h₁ a) * (∑ b : α₂, h₂ b) := by
  simp +decide only [← mul_sum, ← sum_mul]

/-
Factoring out a constant from the inner sum.
-/
lemma sum_sum_const_factor {α₁ α₂ : Type*} [Fintype α₁] [Fintype α₂]
    (h₁ : α₁ → ℝ≥0∞) (h₂ : α₂ → ℝ≥0∞) :
    (∑ a : α₁, ∑ b : α₂, h₁ a * h₂ b) =
    ∑ a : α₁, h₁ a * (∑ b : α₂, h₂ b) := by
  simp +decide only [Finset.mul_sum _ _ _]

/-
Factoring the intersection sum when indicators depend on complementary coordinates
-/
lemma factor_intersection_sum
    (S : Finset ι) (g : ∀ i, β i → ℝ≥0∞) (hg : ∀ i, ∑ b, g i b = 1)
    (C D : Set (∀ i, β i))
    (hC : ∀ f₁ f₂ : ∀ i, β i, (∀ i ∈ S, f₁ i = f₂ i) → (f₁ ∈ C ↔ f₂ ∈ C))
    (hD : ∀ f₁ f₂ : ∀ i, β i, (∀ i, i ∉ S → f₁ i = f₂ i) → (f₁ ∈ D ↔ f₂ ∈ D)) :
    (∑ f : ∀ i, β i, if f ∈ C ∩ D then ∏ i, g i (f i) else 0) =
    (∑ f : ∀ i, β i, if f ∈ C then ∏ i, g i (f i) else 0) *
    (∑ f : ∀ i, β i, if f ∈ D then ∏ i, g i (f i) else 0) := by
  set p : ι → Prop := (· ∈ (S : Set ι))
  -- C-membership depends only on the p-component
  have hC_dep : ∀ (f_S : ∀ i : {x // p x}, β ↑i)
      (f_Sc f_Sc' : ∀ i : {x // ¬p x}, β ↑i),
      (Equiv.piEquivPiSubtypeProd p β).symm (f_S, f_Sc) ∈ C ↔
      (Equiv.piEquivPiSubtypeProd p β).symm (f_S, f_Sc') ∈ C := by
    intro f_S f_Sc f_Sc'
    apply hC; intro i hi
    exact pi_symm_agree_on_yes p f_S f_Sc f_Sc' i hi
  -- D-membership depends only on the ¬p-component
  have hD_dep : ∀ (f_S f_S' : ∀ i : {x // p x}, β ↑i)
      (f_Sc : ∀ i : {x // ¬p x}, β ↑i),
      (Equiv.piEquivPiSubtypeProd p β).symm (f_S, f_Sc) ∈ D ↔
      (Equiv.piEquivPiSubtypeProd p β).symm (f_S', f_Sc) ∈ D := by
    intro f_S f_S' f_Sc
    apply hD; intro i hi
    exact pi_symm_agree_on_no p f_S f_S' f_Sc i hi
  -- Define the two factors
  -- Derive Nonempty instances from hg
  have hne : ∀ i, Nonempty (β i) := by
    intro i; by_contra h; rw [not_nonempty_iff] at h
    have := hg i; rw [Finset.sum_eq_zero] at this
    · exact one_ne_zero this.symm
    · intro x; exact (h.false x).elim
  -- Pick a default element for each β i
  set dflt_S : ∀ i : {x // p x}, β ↑i := fun i => (hne ↑i).some
  set dflt_Sc : ∀ i : {x // ¬p x}, β ↑i := fun i => (hne ↑i).some
  set fC : (∀ i : {x // p x}, β ↑i) → ℝ≥0∞ :=
    fun f_S => if (Equiv.piEquivPiSubtypeProd p β).symm (f_S, dflt_Sc) ∈ C
      then ∏ i : {x // p x}, g ↑i (f_S i) else 0
  set fD : (∀ i : {x // ¬p x}, β ↑i) → ℝ≥0∞ :=
    fun f_Sc => if (Equiv.piEquivPiSubtypeProd p β).symm (dflt_S, f_Sc) ∈ D
      then ∏ i : {x // ¬p x}, g ↑i (f_Sc i) else 0
  -- Step 1: LHS = ∑_{f_S} ∑_{f_Sc} fC(f_S) * fD(f_Sc)
  have lhs_eq : (∑ f, if f ∈ C ∩ D then ∏ i, g i (f i) else 0) =
      ∑ f_S, ∑ f_Sc, fC f_S * fD f_Sc := by
    -- Use sum_pi_decompose to rewrite the sum over all functions as a double sum over the two subtypes.
    have h_double_sum : ∑ f : ∀ i, β i, (if f ∈ C ∩ D then ∏ i, g i (f i) else 0) = ∑ f_S : ∀ i : {x // p x}, β ↑i, ∑ f_Sc : ∀ i : {x // ¬p x}, β ↑i, (if (Equiv.piEquivPiSubtypeProd p β).symm (f_S, f_Sc) ∈ C ∩ D then ∏ i, g i ((Equiv.piEquivPiSubtypeProd
 p β).symm (f_S, f_Sc) i) else 0) := by
      convert sum_pi_decompose p _ using 1;
      convert rfl;
    convert h_double_sum using 3;
    simp +zetaDelta at *;
    split_ifs <;> simp_all +decide only [];
    · convert prod_pi_decompose p g _ _ |> Eq.symm;
      grind +revert;
    · grind +ring;
    · grind +ring;
    · grind
  -- Step 2: RHS_C = (∑ fC) * 1
  have rhs_C_eq : (∑ f, if f ∈ C then ∏ i, g i (f i) else 0) =
      ∑ f_S, fC f_S := by
    have h_sum_fC : (∑ f, if f ∈ C then ∏ i, g i (f i) else 0) =
                        ∑ f_S : ∀ i : {x // p x}, β ↑i,
                          ∑ f_Sc : ∀ i : {x // ¬p x}, β ↑i,
                            (if (Equiv.piEquivPiSubtypeProd p β).symm (f_S, f_Sc) ∈ C then ∏ i : ι, g i ((Equiv.piEquivPiSubtypeProd p β).symm (f_S, f_Sc) i) else 0) := by
                              convert sum_pi_decompose p _ using 1;
                              convert rfl;
    rw [h_sum_fC];
    refine' Finset.sum_congr rfl fun f_S _ => _;
    rw [ Finset.sum_congr rfl fun f_Sc _ => if_congr ( hC_dep f_S f_Sc dflt_Sc ) rfl rfl ];
    rw [ Finset.sum_congr rfl fun f_Sc _ => ?_ ];
    any_goals exact fun f_Sc => if ( Equiv.piEquivPiSubtypeProd p β ).symm ( f_S, dflt_Sc ) ∈ C then ( ∏ i : { x // p x }, g ( i : ι ) ( f_S i ) ) * ( ∏ i : { x // ¬p x }, g ( i : ι ) ( f_Sc i ) ) else 0;
    · by_cases h : ( Equiv.piEquivPiSubtypeProd p β ).symm ( f_S, dflt_Sc ) ∈ C <;> simp +decide [ h ];
      · simp +zetaDelta at *;
        rw [ ← Finset.mul_sum _ _ _, sum_subtype_pi_prod, prod_subtype_sum_one ] <;> simp +decide [ hg, h ];
      · exact Eq.symm ( if_neg h );
    · rw [ prod_pi_decompose ];
      convert rfl
  -- Step 3: RHS_D = 1 * (∑ fD)
  have rhs_D_eq : (∑ f, if f ∈ D then ∏ i, g i (f i) else 0) =
      ∑ f_Sc, fD f_Sc := by
    -- Apply the sum_pi_decompose lemma to split the sum into a sum over f_Sc and a sum over f_S.
    have h_split : (∑ f : ∀ i, β i, if f ∈ D then ∏ i, g i (f i) else 0) = (∑ f_Sc : ∀ i : {x // ¬p x}, β ↑i, ∑ f_S : ∀ i : {x // p x}, β ↑i, if (Equiv.piEquivPiSubtypeProd p β).symm (f_S, f_Sc) ∈ D then (∏ i : {x // p x}, g ↑i (f_S i)) * (∏ i : {x // ¬p
 x}, g ↑i (f_Sc i)) else 0) := by
      rw [ ← Finset.sum_comm, sum_pi_decompose p ];
      congr! 3;
      convert prod_pi_decompose p g _ _ using 1;
      convert rfl;
    -- By the properties of the sum and the definition of fD, we can simplify the expression.
    have h_simplify : ∀ f_Sc : ∀ i : {x // ¬p x}, β ↑i, (∑ f_S : ∀ i : {x // p x}, β ↑i, if (Equiv.piEquivPiSubtypeProd p β).symm (f_S, f_Sc) ∈ D then (∏ i : {x // p x}, g ↑i (f_S i)) else 0) = if (Equiv.piEquivPiSubtypeProd p β).symm (dflt_S, f_Sc) ∈ D then 1 else 0 := by
      intro f_Sc
      by_cases h : (Equiv.piEquivPiSubtypeProd p β).symm (dflt_S, f_Sc) ∈ D;
      · rw [ Finset.sum_congr rfl fun f_S _ => if_pos <| hD_dep f_S dflt_S f_Sc |>.2 h ];
        convert sum_subtype_pi_prod p g using 1;
        · convert rfl;
        · simp +decide [ h, hg ];
      · simp [h];
        exact fun f hf => False.elim <| h <| hD_dep f dflt_S f_Sc |>.1 hf;
    rw [ h_split ];
    refine' Finset.sum_congr rfl fun f_Sc _ => _;
    convert congr_arg ( · * ∏ i : { x // ¬p x }, g ( i : ) ( f_Sc i ) ) ( h_simplify f_Sc ) using 1;
    · rw [ Finset.sum_mul _ _ _ ] ; congr ; ext ; split_ifs <;> ring;
    · simp +zetaDelta at *
  -- Combine
  rw [lhs_eq, rhs_C_eq, rhs_D_eq, sum_prod_mul_factor]

/-- Main product independence theorem. -/
theorem product_independence_thm
    (g : ∀ i, β i → ℝ≥0∞)
    (hg : ∀ i, ∑ b, g i b = 1)
    (A B : Set (∀ i, β i))
    (S T : Finset ι)
    (hST : Disjoint S T)
    (hA : ∀ f₁ f₂ : ∀ i, β i, (∀ i ∈ S, f₁ i = f₂ i) → (f₁ ∈ A ↔ f₂ ∈ A))
    (hB : ∀ f₁ f₂ : ∀ i, β i, (∀ i ∈ T, f₁ i = f₂ i) → (f₁ ∈ B ↔ f₂ ∈ B)) :
    (∑ f : ∀ i, β i, if f ∈ A ∩ B then ∏ i, g i (f i) else 0) =
    (∑ f : ∀ i, β i, if f ∈ A then ∏ i, g i (f i) else 0) *
    (∑ f : ∀ i, β i, if f ∈ B then ∏ i, g i (f i) else 0) := by
  have hB' : ∀ f₁ f₂ : ∀ i, β i, (∀ i, i ∉ S → f₁ i = f₂ i) → (f₁ ∈ B ↔ f₂ ∈ B) := by
    intro f₁ f₂ h
    exact hB f₁ f₂ (fun i hi => h i (fun hmem => Finset.disjoint_right.mp hST hi hmem))
  exact factor_intersection_sum S g hg A B hA hB'

/-
In the product measure, the probability of {f | f(i₀) = b₀} equals g(i₀, b₀).
-/
lemma single_coord_prob [∀ i, DecidableEq (β i)] (g : ∀ i, β i → ℝ≥0∞) (hg : ∀ i, ∑ b, g i b = 1)
    (i₀ : ι) (b₀ : β i₀) :
    (∑ f : ∀ i, β i, if f i₀ = b₀ then ∏ i, g i (f i) else (0 : ℝ≥0∞)) = g i₀ b₀ := by
  -- Apply the decomposition lemma with the predicate p(i) = (i = i₀).
  have h_decomp : ∑ f : ∀ i, β i, (if f i₀ = b₀ then ∏ i, g i (f i) else 0) =
    ∑ f_yes : ∀ i : {x // x = i₀}, β ↑i, ∑ f_no : ∀ i : {x // ¬x = i₀}, β ↑i, (if (Equiv.piEquivPiSubtypeProd (fun i => i = i₀) β).symm (f_yes, f_no) i₀ = b₀ then ∏ i, g i ((Equiv.piEquivPiSubtypeProd (fun i => i = i₀) β).symm (f_yes, f_no) i) else 0) :=
 by
      convert sum_pi_decompose ( fun i => i = i₀ ) _ using 1;
      convert rfl;
  -- The condition f(i₀) = b₀ only depends on f_yes. In fact, f_yes is uniquely determined by f_yes ⟨i₀, rfl⟩ : β i₀. The condition becomes f_yes ⟨i₀, rfl⟩ = b₀ (modulo the equivalence).
  have h_fyes : ∑ f_yes : ∀ i : {x // x = i₀}, β ↑i, ∑ f_no : ∀ i : {x // ¬x = i₀}, β ↑i, (if f_yes ⟨i₀, rfl⟩ = b₀ then ∏ i : {x // x = i₀}, g ↑i (f_yes i) * ∏ i : {x // ¬x = i₀}, g ↑i (f_no i) else 0) = ∑ f_yes : ∀ i : {x // x = i₀}, β ↑i, (if f_yes ⟨i₀, rfl⟩ = b₀ then ∏ i : {x // x = i₀}, g ↑i (f_yes i) else 0) * ∏ i : {x // ¬x = i₀}, ∑ b : β ↑i, g ↑i b := by
    simp +decide [ Finset.prod_mul_distrib ];
    simp +decide only [← Finset.mul_sum _ _ _, ← sum_subtype_pi_prod];
  -- The sum over f_yes simplifies to g(i₀, b₀) because there's only one f_yes that satisfies the condition.
  have h_fyes_simplified : ∑ f_yes : ∀ i : {x // x = i₀}, β ↑i, (if f_yes ⟨i₀, rfl⟩ = b₀ then ∏ i : {x // x = i₀}, g ↑i (f_yes i) else 0) = g i₀ b₀ := by
    rw [ Finset.sum_eq_single ( fun ⟨ i, hi ⟩ => if hi : i = i₀ then by subst hi; exact b₀ else by tauto ) ] <;> simp +decide;
    · grind +extAll;
    · intro b hb hb'; contrapose! hb; aesop;
  convert h_fyes using 1;
  · convert h_decomp using 3;
    rw [ prod_pi_decompose ];
    simp +decide [ Equiv.piEquivPiSubtypeProd ];
  · rw [ ← Finset.sum_mul _ _ _, h_fyes_simplified, prod_subtype_sum_one _ g hg, mul_one ]

/-
In the product measure, the probability of f(i₀) ∈ S₀ equals ∑_{b₀ ∈ S₀} g(i₀, b₀).
-/
lemma single_coord_set_prob [∀ i, DecidableEq (β i)] (g : ∀ i, β i → ℝ≥0∞) (hg : ∀ i, ∑ b, g i b = 1)
    (i₀ : ι) (S₀ : Finset (β i₀)) :
    (∑ f : ∀ i, β i, if f i₀ ∈ S₀ then ∏ i, g i (f i) else (0 : ℝ≥0∞)) =
    ∑ b₀ ∈ S₀, g i₀ b₀ := by
  have hsc := single_coord_prob g hg i₀
  conv_lhs =>
    arg 2; ext f
    rw [show (if f i₀ ∈ S₀ then ∏ i, g i (f i) else 0) =
        ∑ b₀ ∈ S₀, if f i₀ = b₀ then ∏ i, g i (f i) else 0 from by
      rw [← Finset.sum_ite_eq S₀ (f i₀) (fun _ => ∏ i, g i (f i))]]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b₀ _ => hsc b₀

/-- Set version of two_coord_prob: probability of f(i₁) ∈ S₁ ∧ f(i₂) ∈ S₂. -/
lemma two_coord_set_prob [∀ i, DecidableEq (β i)] (g : ∀ i, β i → ℝ≥0∞) (hg : ∀ i, ∑ b, g i b = 1)
    (i₁ i₂ : ι) (hi : i₁ ≠ i₂) (S₁ : Finset (β i₁)) (S₂ : Finset (β i₂)) :
    (∑ f : ∀ i, β i, if f i₁ ∈ S₁ ∧ f i₂ ∈ S₂ then ∏ i, g i (f i) else (0 : ℝ≥0∞)) =
    (∑ b₁ ∈ S₁, g i₁ b₁) * (∑ b₂ ∈ S₂, g i₂ b₂) := by
  rw [← single_coord_set_prob g hg i₁ S₁, ← single_coord_set_prob g hg i₂ S₂]
  have key := product_independence_thm g hg {f | f i₁ ∈ S₁} {f | f i₂ ∈ S₂} {i₁} {i₂}
    (Finset.disjoint_singleton.mpr hi)
    (fun f₁ f₂ h => by simp [Set.mem_setOf_eq]; rw [h i₁ (Finset.mem_singleton.mpr rfl)])
    (fun f₁ f₂ h => by simp [Set.mem_setOf_eq]; rw [h i₂ (Finset.mem_singleton.mpr rfl)])
  convert key using 3 <;> simp [Set.mem_setOf_eq]

/-
In the product measure, the probability of fixing two coordinates
    at given values equals the product of the individual weights, when the
    coordinates are distinct.
-/
lemma two_coord_prob [∀ i, DecidableEq (β i)] (g : ∀ i, β i → ℝ≥0∞) (hg : ∀ i, ∑ b, g i b = 1)
    (i₁ i₂ : ι) (hi : i₁ ≠ i₂) (b₁ : β i₁) (b₂ : β i₂) :
    (∑ f : ∀ i, β i, if f i₁ = b₁ ∧ f i₂ = b₂ then ∏ i, g i (f i) else (0 : ℝ≥0∞)) =
    g i₁ b₁ * g i₂ b₂ := by
  convert product_independence_thm g hg { f | f i₁ = b₁ } { f | f i₂ = b₂ } { i₁ } { i₂ } _ _ _ using 1 <;> simp +decide [ * ];
  · rw [ ← single_coord_prob g hg i₁ b₁, ← single_coord_prob g hg i₂ b₂ ];
    convert rfl;
  · grind;
  · grind

/-- Three-coord factorization: f(i₁) = b₁ ∧ f(i₂) = b₂ ∧ f(i₃) ∈ S₃. -/
lemma three_coord_mixed_prob [∀ i, DecidableEq (β i)] (g : ∀ i, β i → ℝ≥0∞) (hg : ∀ i, ∑ b, g i b = 1)
    (i₁ i₂ i₃ : ι) (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    (b₁ : β i₁) (b₂ : β i₂) (S₃ : Finset (β i₃)) :
    (∑ f : ∀ i, β i, if f i₁ = b₁ ∧ f i₂ = b₂ ∧ f i₃ ∈ S₃ then ∏ i, g i (f i) else (0 : ℝ≥0∞)) =
    g i₁ b₁ * g i₂ b₂ * (∑ b₃ ∈ S₃, g i₃ b₃) := by
  rw [← two_coord_prob g hg i₁ i₂ h₁₂ b₁ b₂, ← single_coord_set_prob g hg i₃ S₃]
  have hST : Disjoint ({i₁, i₂} : Finset ι) {i₃} := by
    rw [Finset.disjoint_iff_ne]; intro a ha b hb
    simp at ha hb; subst hb; rcases ha with rfl | rfl <;> assumption
  have key := product_independence_thm g hg {f | f i₁ = b₁ ∧ f i₂ = b₂} {f | f i₃ ∈ S₃} {i₁, i₂} {i₃}
    hST
    (fun f₁ f₂ h => by
      simp only [Set.mem_setOf_eq]
      constructor <;> intro ⟨ha, hb⟩ <;> constructor
      all_goals first
        | (rw [← h i₁ (by simp)]; exact ha)
        | (rw [← h i₂ (by simp)]; exact hb)
        | (rw [h i₁ (by simp)]; exact ha)
        | (rw [h i₂ (by simp)]; exact hb))
    (fun f₁ f₂ h => by simp [Set.mem_setOf_eq]; rw [h i₃ (Finset.mem_singleton.mpr rfl)])
  convert key using 3 <;> simp [Set.mem_setOf_eq, and_assoc]

end
