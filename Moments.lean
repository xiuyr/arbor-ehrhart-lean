module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators

namespace ArborCounterexample

noncomputable section

def moment {α : Type} [Fintype α] (d : α → ℕ) (r : ℕ) : ℚ :=
  ∑ a, (d a : ℚ)^r

abbrev Lift {α : Type} (m : ℕ) (d : α → ℕ) := Σ a : α, Fin (m+d a+1)
instance {α : Type} [Fintype α] (m : ℕ) (d : α → ℕ) : Fintype (Lift m d) :=
  inferInstanceAs (Fintype (Sigma fun a : α => Fin (m+d a+1)))
def liftDef {α : Type} {m : ℕ} {d : α → ℕ} (a : Lift m d) : ℕ := a.2.val

theorem sum_powers (m : ℕ) :
    (∑ d : Fin (m+1), (d.val : ℚ)) = m*(m+1)/2 ∧
    (∑ d : Fin (m+1), (d.val : ℚ)^2) = m*(m+1)*(2*m+1)/6 ∧
    (∑ d : Fin (m+1), (d.val : ℚ)^3) = m^2*(m+1)^2/4 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rcases ih with ⟨h1,h2,h3⟩
    refine ⟨?_,?_,?_⟩
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
      rw [h1]
      ring
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
      rw [h2]
      ring
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
      rw [h3]
      ring

theorem lift_moment0 {α : Type} [Fintype α] (m : ℕ) (d : α → ℕ) :
    moment (@liftDef α m d) 0 = (m+1)*moment d 0+moment d 1 := by
  simp [moment, liftDef, Lift, Fintype.sum_sigma, Nat.cast_add,
    Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  ring

theorem lift_moment1 {α : Type} [Fintype α] (m : ℕ) (d : α → ℕ) :
    moment (@liftDef α m d) 1 =
      (m*(m+1)*moment d 0+(2*m+1)*moment d 1+moment d 2)/2 := by
  simp only [moment, Lift, liftDef, Fintype.sum_sigma, pow_one]
  simp_rw [(sum_powers (m+d _)).1, Nat.cast_add]
  simp only [pow_zero, Finset.sum_const, nsmul_eq_mul]
  simp_rw [show ∀ a : α, ((m:ℚ)+d a)*((m:ℚ)+d a+1)/2 =
    (m*(m+1)+(2*m+1)*d a+(d a)^2)/2 by intro a; ring]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
    Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  ring

theorem lift_moment2 {α : Type} [Fintype α] (m : ℕ) (d : α → ℕ) :
    moment (@liftDef α m d) 2 =
      ((2*m^3+3*m^2+m)*moment d 0+(6*m^2+6*m+1)*moment d 1+
       (6*m+3)*moment d 2+2*moment d 3)/6 := by
  simp only [moment, Lift, liftDef, Fintype.sum_sigma]
  simp_rw [(sum_powers (m+d _)).2.1, Nat.cast_add]
  simp only [pow_zero, pow_one, Finset.sum_const, nsmul_eq_mul]
  simp_rw [show ∀ a : α,
    ((m:ℚ)+d a)*((m:ℚ)+d a+1)*(2*((m:ℚ)+d a)+1)/6 =
      ((2*m^3+3*m^2+m)+(6*m^2+6*m+1)*d a+
       (6*m+3)*(d a)^2+2*(d a)^3)/6 by intro a; ring]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
    Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  ring

theorem prod_moment0 {α β : Type} [Fintype α] [Fintype β]
    (d : α → ℕ) (e : β → ℕ) :
    moment (fun a : α × β => d a.1+e a.2) 0 = moment d 0*moment e 0 := by
  simp [moment, Fintype.card_prod, Nat.cast_mul]

theorem prod_moment1 {α β : Type} [Fintype α] [Fintype β]
    (d : α → ℕ) (e : β → ℕ) :
    moment (fun a : α × β => d a.1+e a.2) 1 =
      moment d 1*moment e 0+moment d 0*moment e 1 := by
  simp [moment, Fintype.sum_prod_type, Nat.cast_add,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  ring

theorem prod_moment2 {α β : Type} [Fintype α] [Fintype β]
    (d : α → ℕ) (e : β → ℕ) :
    moment (fun a : α × β => d a.1+e a.2) 2 =
      moment d 2*moment e 0+2*moment d 1*moment e 1+moment d 0*moment e 2 := by
  simp only [moment, Fintype.sum_prod_type, Nat.cast_add, add_sq, pow_zero, pow_one]
  simp_rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring_nf
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring

theorem prod_moment3 {α β : Type} [Fintype α] [Fintype β]
    (d : α → ℕ) (e : β → ℕ) :
    moment (fun a : α × β => d a.1+e a.2) 3 =
      moment d 3*moment e 0+3*moment d 2*moment e 1+
      3*moment d 1*moment e 2+moment d 0*moment e 3 := by
  simp only [moment, Fintype.sum_prod_type, Nat.cast_add, pow_zero, pow_one]
  simp_rw [show ∀ a : α, ∀ b : β, ((d a : ℚ)+(e b : ℚ))^3 =
    (d a : ℚ)^3+3*(d a : ℚ)^2*(e b : ℚ)+
    3*(d a : ℚ)*(e b : ℚ)^2+(e b : ℚ)^3 by intros; ring]
  simp_rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring_nf
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring

end
end ArborCounterexample
