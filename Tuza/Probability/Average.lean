import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! Finite rational averages and uniformly chosen Boolean vertex colorings. -/

namespace Tuza

open scoped BigOperators

variable {Ω : Type*} {Ω' : Type*} {I : Type*} {V : Type*}

/-- The uniform average on a finite type, with values in the rationals. -/
def finiteAverage [Fintype Ω] (f : Ω → ℚ) : ℚ :=
  (∑ ω, f ω) / Fintype.card Ω

/-- The uniform average over all Boolean vertex colorings. -/
def bitAverage [Fintype V] [DecidableEq V] (f : (V → Bool) → ℚ) : ℚ :=
  finiteAverage f

theorem finiteAverage_equiv [Fintype Ω] [Fintype Ω']
    (e : Ω ≃ Ω') (f : Ω' → ℚ) :
    finiteAverage (fun ω => f (e ω)) = finiteAverage f := by
  unfold finiteAverage
  rw [e.sum_comp, Fintype.card_congr e]

theorem finiteAverage_const [Fintype Ω] [Nonempty Ω] (c : ℚ) :
    finiteAverage (fun _ : Ω => c) = c := by
  have hn : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [finiteAverage, hn]

theorem finiteAverage_add [Fintype Ω] (f g : Ω → ℚ) :
    finiteAverage (fun ω => f ω + g ω) = finiteAverage f + finiteAverage g := by
  simp only [finiteAverage, Finset.sum_add_distrib, add_div]

theorem finiteAverage_finset_sum [Fintype Ω] (s : Finset I) (f : I → Ω → ℚ) :
    finiteAverage (fun ω => ∑ i ∈ s, f i ω) =
      ∑ i ∈ s, finiteAverage (f i) := by
  unfold finiteAverage
  rw [Finset.sum_comm, Finset.sum_div]

theorem finiteAverage_sum [Fintype Ω] [Fintype I] (f : I → Ω → ℚ) :
    finiteAverage (fun ω => ∑ i, f i ω) = ∑ i, finiteAverage (f i) := by
  exact finiteAverage_finset_sum Finset.univ f

theorem finiteAverage_mono [Fintype Ω] (f g : Ω → ℚ)
    (h : ∀ ω, f ω ≤ g ω) : finiteAverage f ≤ finiteAverage g := by
  unfold finiteAverage
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun ω _ => h ω)
    (by positivity)

/-- Some outcome costs no more than its uniform finite average. -/
theorem exists_le_finiteAverage [Fintype Ω] [Nonempty Ω] (f : Ω → ℚ) :
    ∃ ω, f ω ≤ finiteAverage f := by
  classical
  obtain ⟨ω, _, hω⟩ :=
    Finset.exists_min_image (Finset.univ : Finset Ω) f Finset.univ_nonempty
  refine ⟨ω, ?_⟩
  have hn : (0 : ℚ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos
  apply (le_div_iff₀ hn).2
  calc
    f ω * (Fintype.card Ω : ℚ) = ∑ _ : Ω, f ω := by simp [mul_comm]
    _ ≤ ∑ a : Ω, f a := Finset.sum_le_sum fun a ha => hω a ha

/-- Finite-sum accounting: pointwise charges and individual average bounds
produce one outcome obeying the sum of the budgets. -/
theorem exists_le_sum_of_average_le [Fintype Ω] [Nonempty Ω]
    (s : Finset I) (cost : Ω → ℚ) (base : ℚ)
    (charge : I → Ω → ℚ) (budget : I → ℚ)
    (hcost : ∀ ω, cost ω ≤ base + ∑ i ∈ s, charge i ω)
    (hcharge : ∀ i ∈ s, finiteAverage (charge i) ≤ budget i) :
    ∃ ω, cost ω ≤ base + ∑ i ∈ s, budget i := by
  obtain ⟨ω, hω⟩ := exists_le_finiteAverage cost
  refine ⟨ω, hω.trans ?_⟩
  calc
    finiteAverage cost ≤
        finiteAverage (fun ω => base + ∑ i ∈ s, charge i ω) :=
      finiteAverage_mono _ _ hcost
    _ = base + ∑ i ∈ s, finiteAverage (charge i) := by
      rw [finiteAverage_add, finiteAverage_const, finiteAverage_finset_sum]
    _ ≤ base + ∑ i ∈ s, budget i :=
      add_le_add_right (Finset.sum_le_sum hcharge) base

private theorem finiteAverage_prod_fst [Fintype Ω] [Fintype Ω']
    [Nonempty Ω] [Nonempty Ω'] (f : Ω → ℚ) :
    finiteAverage (fun p : Ω × Ω' => f p.1) = finiteAverage f := by
  have ha : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hb : (Fintype.card Ω' : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold finiteAverage
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_prod, Nat.cast_mul]
  rw [← Finset.mul_sum]
  field_simp

/-- Uniform Boolean colorings restrict uniformly to any list of distinct
vertices.  This is the finite independence statement used below. -/
theorem bitAverage_restrict [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (v : I → V) (hv : Function.Injective v) (f : (I → Bool) → ℚ) :
    bitAverage (fun χ : V → Bool => f (χ ∘ v)) = bitAverage f := by
  letI : DecidablePred (fun a : V => a ∈ Set.range v) :=
    fun _ => Classical.propDecidable _
  let e : (V → Bool) ≃
      (I → Bool) × ({a : V // a ∉ Set.range v} → Bool) :=
    (Equiv.piEquivPiSubtypeProd (fun a => a ∈ Set.range v) (fun _ => Bool)).trans
      (Equiv.prodCongr
        (Equiv.arrowCongr (Equiv.ofInjective v hv).symm (Equiv.refl Bool))
        (Equiv.refl _))
  have he (χ : V → Bool) : (e χ).1 = χ ∘ v := by
    rfl
  change finiteAverage (fun χ : V → Bool => f (χ ∘ v)) = finiteAverage f
  calc
    finiteAverage (fun χ : V → Bool => f (χ ∘ v)) =
        finiteAverage (fun χ : V → Bool => f (e χ).1) := by
      simp only [he]
    _ = finiteAverage (fun p :
        (I → Bool) × ({a : V // a ∉ Set.range v} → Bool) => f p.1) :=
      finiteAverage_equiv e (fun p => f p.1)
    _ = finiteAverage f := finiteAverage_prod_fst f

/-- An edge is noncrossing when its endpoints have the same Boolean color. -/
def sameColor (u v : V) (χ : V → Bool) : Prop := χ u = χ v

/-- The event allowing an opposite edge of a two-page book to be added. -/
def bookEvent (u v x y : V) (χ : V → Bool) : Prop :=
  χ x = χ y ∧ (χ u ≠ χ x ∨ χ v ≠ χ x)

instance (u v : V) : DecidablePred (sameColor u v) :=
  fun _ => inferInstanceAs (Decidable (_ = _))

instance (u v x y : V) : DecidablePred (bookEvent u v x y) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ (_ ∨ _)))

/-- Two distinct vertices agree in exactly half of all Boolean colorings. -/
theorem sameColor_average [Fintype V] [DecidableEq V] (u v : V) (huv : u ≠ v) :
    bitAverage (fun χ => if sameColor u v χ then (1 : ℚ) else 0) = 1 / 2 := by
  have hi : Function.Injective (![u, v] : Fin 2 → V) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h := bitAverage_restrict (![u, v] : Fin 2 → V) hi
    (fun χ => if χ 0 = χ 1 then (1 : ℚ) else 0)
  have hsmall : bitAverage
      (fun χ : Fin 2 → Bool => if χ 0 = χ 1 then (1 : ℚ) else 0) = 1 / 2 := by
    decide +kernel
  calc
    bitAverage (fun χ => if sameColor u v χ then (1 : ℚ) else 0) =
        bitAverage (fun χ : V → Bool =>
          if (χ ∘ (![u, v] : Fin 2 → V)) 0 =
              (χ ∘ (![u, v] : Fin 2 → V)) 1 then (1 : ℚ) else 0) := by
      congr 1
    _ = 1 / 2 := h.trans hsmall

/-- The book event occurs in six of the sixteen local Boolean colorings. -/
theorem bookEvent_average_of_injective [Fintype V] [DecidableEq V] (u v x y : V)
    (h : Function.Injective (![u, v, x, y] : Fin 4 → V)) :
    bitAverage (fun χ => if bookEvent u v x y χ then (1 : ℚ) else 0) = 3 / 8 := by
  have hr := bitAverage_restrict (![u, v, x, y] : Fin 4 → V) h
    (fun χ => if χ 2 = χ 3 ∧ (χ 0 ≠ χ 2 ∨ χ 1 ≠ χ 2) then (1 : ℚ) else 0)
  have hsmall : bitAverage (fun χ : Fin 4 → Bool =>
      if χ 2 = χ 3 ∧ (χ 0 ≠ χ 2 ∨ χ 1 ≠ χ 2) then (1 : ℚ) else 0) = 3 / 8 := by
    decide +kernel
  calc
    bitAverage (fun χ => if bookEvent u v x y χ then (1 : ℚ) else 0) =
        bitAverage (fun χ : V → Bool =>
          if (χ ∘ (![u, v, x, y] : Fin 4 → V)) 2 =
              (χ ∘ (![u, v, x, y] : Fin 4 → V)) 3 ∧
            ((χ ∘ (![u, v, x, y] : Fin 4 → V)) 0 ≠
              (χ ∘ (![u, v, x, y] : Fin 4 → V)) 2 ∨
             (χ ∘ (![u, v, x, y] : Fin 4 → V)) 1 ≠
              (χ ∘ (![u, v, x, y] : Fin 4 → V)) 2) then (1 : ℚ) else 0) := by
      congr 1
    _ = 3 / 8 := hr.trans hsmall

theorem bookEvent_average [Fintype V] [DecidableEq V] (u v x y : V)
    (huv : u ≠ v) (hux : u ≠ x) (huy : u ≠ y)
    (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y) :
    bitAverage (fun χ => if bookEvent u v x y χ then (1 : ℚ) else 0) = 3 / 8 := by
  apply bookEvent_average_of_injective
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

end Tuza
