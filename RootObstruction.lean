module

public import ComplexFTA
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push

@[expose] public section

open Polynomial

namespace ArborCounterexample

noncomputable def f : Polynomial ℝ :=
  C 24 + C 5852 * X + C 400056 * X^2 + C 8533751 * X^3 +
    C 44368122 * X^4 + C 67184474 * X^5

noncomputable def laguerre (p : Polynomial ℝ) (x : ℝ) : ℝ :=
  p.derivative.eval x ^ 2 - p.eval x * p.derivative.derivative.eval x

theorem laguerre_mul (p q : Polynomial ℝ) (x : ℝ) :
    laguerre (p*q) x = q.eval x ^ 2 * laguerre p x +
      p.eval x ^ 2 * laguerre q x := by
  simp only [laguerre, derivative_mul, derivative_add, eval_add, eval_mul]
  ring

theorem laguerre_C (c x : ℝ) : laguerre (C c) x = 0 := by
  simp [laguerre]

theorem laguerre_linear (r x : ℝ) : laguerre (X-C r) x = 1 := by
  simp [laguerre]

theorem laguerre_prod_nonneg (rs : Multiset ℝ) (x : ℝ) :
    0 ≤ laguerre ((rs.map fun r => X-C r).prod) x := by
  induction rs using Multiset.induction_on with
  | empty => simp [laguerre]
  | @cons r rs ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [laguerre_mul, laguerre_linear]
    positivity

theorem laguerre_nonneg_of_splits (p : Polynomial ℝ) (hp : p.Splits) (x : ℝ) :
    0 ≤ laguerre p x := by
  rw [hp.eq_prod_roots, laguerre_mul, laguerre_C]
  have := laguerre_prod_nonneg p.roots x
  positivity

theorem f_laguerre_negative : laguerre f (-(3:ℝ)/10) =
    -(41123948517599:ℝ)/1000000 := by
  simp only [laguerre, f, derivative_add, derivative_mul, derivative_pow,
    derivative_C, derivative_X, derivative_one, eval_add, eval_mul, eval_pow,
    eval_C, eval_X, eval_one, eval_zero, derivative_zero]
  norm_num

theorem f_not_splits : ¬ f.Splits := by
  intro h
  have hn := laguerre_nonneg_of_splits f h (-(3:ℝ)/10)
  rw [f_laguerre_negative] at hn
  norm_num at hn

theorem f_has_nonreal_root : ∃ z : ℂ, (f.map (algebraMap ℝ ℂ)).eval z = 0 ∧ z.im ≠ 0 := by
  by_contra h
  push Not at h
  apply f_not_splits
  apply Polynomial.Splits.of_splits_map_of_injective (algebraMap ℝ ℂ).injective
    (IsAlgClosed.splits _)
  intro z hz
  have hf : f.map (algebraMap ℝ ℂ) ≠ 0 := by
    intro he
    have he0 := congrArg (fun p : Polynomial ℂ => p.eval 0) he
    norm_num [f] at he0
  have hz0 := (Polynomial.mem_roots hf).mp hz
  have him := h z hz0
  refine ⟨z.re, ?_⟩
  apply Complex.ext <;> simp [him]

#print axioms f_has_nonreal_root

end ArborCounterexample
