import Mathlib

noncomputable section
namespace CanonicalRoots
open Polynomial

theorem polynomial_first_jet_identity (P Q U V : Polynomial ℂ) (q : ℂ)
    (h : P * Q = U * V) (hQ : Q.eval q = 0) (hV : V.eval q = 0) :
    P.eval q * Q.derivative.eval q = U.eval q * V.derivative.eval q := by
  have he := congrArg (fun f : Polynomial ℂ => f.derivative.eval q) h
  simpa only [derivative_mul, eval_add, eval_mul, hQ, hV, mul_zero, zero_add] using he

theorem polynomial_second_jet_identity (P Q U V : Polynomial ℂ) (q : ℂ)
    (h : P * Q = U * V) (hQ : Q.eval q = 0) (hQ' : Q.derivative.eval q = 0)
    (hU : U.eval q = 0) (hV : V.eval q = 0) :
    P.eval q * Q.derivative.derivative.eval q =
      2 * U.derivative.eval q * V.derivative.eval q := by
  have he := congrArg (fun f : Polynomial ℂ => f.derivative.derivative.eval q) h
  simp only [derivative_mul, derivative_add, eval_add, eval_mul,
    hQ, hQ', hU, hV, mul_zero, zero_mul, zero_add, add_zero] at he
  linear_combination he

theorem derivative_one_sub_X_pow_scaled (n : ℕ) (q : ℂ) :
    q * (1 - (X : Polynomial ℂ) ^ n).derivative.eval q = -(n : ℂ) * q ^ n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [derivative_sub, derivative_one, derivative_X_pow_succ]
    simp only [eval_sub, eval_neg, eval_zero, eval_mul, eval_C, eval_pow, eval_X, zero_sub,
      Nat.cast_add, Nat.cast_one, pow_succ]
    ring

theorem polynomial_three_factor_first_jet (f g h : Polynomial ℂ) (q : ℂ)
    (hf : f.eval q = 0) :
    (f * g * h).derivative.eval q = f.derivative.eval q * g.eval q * h.eval q := by
  simp [derivative_mul, hf]

theorem polynomial_three_factor_second_jet (f g h : Polynomial ℂ) (q : ℂ)
    (hf : f.eval q = 0) (hg : g.eval q = 0) :
    (f * g * h).derivative.derivative.eval q =
      2 * f.derivative.eval q * g.derivative.eval q * h.eval q := by
  simp only [derivative_mul, derivative_add, eval_add, eval_mul, hf, hg,
    mul_zero, zero_mul, zero_add, add_zero]
  ring

end CanonicalRoots
