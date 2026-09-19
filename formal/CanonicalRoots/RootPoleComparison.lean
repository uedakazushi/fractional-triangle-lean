import CanonicalRoots.RootHilbertPoleNumerator
import CanonicalRoots.HypersurfacePoleValue

noncomputable section
namespace CanonicalRoots
open Polynomial

theorem RootHypersurfacePresentation.no_weight_pole {a N : ℕ}
    (p : Fin 3 → ℕ) (hp : AdmissibleSignature p) (ha : 1 ≤ a)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) (P : RootHypersurfacePresentation p τ)
    (hN : 0 < N) (hd : ∀ i, p i ∣ N) (q : ℂ) (hqN : q ^ N = 1) (hq : q ≠ 1)
    (hw : ∀ i, q ^ P.weights i ≠ 1) :
    (∑ i, if q ^ p i = 1 then 1 / ((p i : ℂ) * (1 - q ^ (-(a : ℤ)))) else 0) = 0 := by
  classical
  obtain ⟨S, hpoly, heval⟩ := P.pole_polynomial_identity p hp ha τ hτ hN hd
  have he := congrArg (fun f : Polynomial ℂ => f.eval q) hpoly
  simp only [eval_mul, eval_prod, eval_sub, eval_one, eval_pow, eval_X, hqN,
    sub_self, mul_zero, zero_mul] at he
  have hden : (∏ i, (1 - q ^ P.weights i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => sub_ne_zero.mpr (Ne.symm (hw i)))
  have hzero : S.eval q = 0 := (mul_eq_zero.mp he).resolve_right hden
  rw [heval q hqN hq] at hzero
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  exact (mul_eq_zero.mp hzero).resolve_left
    (mul_ne_zero hN0 (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hq))))

theorem RootHypersurfacePresentation.single_weight_pole {a N : ℕ}
    (p : Fin 3 → ℕ) (hp : AdmissibleSignature p) (ha : 1 ≤ a)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) (P : RootHypersurfacePresentation p τ)
    (hN : 0 < N) (hd : ∀ i, p i ∣ N) (σ : Equiv.Perm (Fin 3))
    (q : ℂ) (hqN : q ^ N = 1) (hq : q ≠ 1)
    (hA : q ^ P.weights (σ 0) = 1) (hB : q ^ P.weights (σ 1) ≠ 1)
    (hC : q ^ P.weights (σ 2) ≠ 1) :
    (∑ i, if q ^ p i = 1 then 1 / ((p i : ℂ) * (1 - q ^ (-(a : ℤ)))) else 0) =
      (1 - q ^ P.relationDegree) /
        ((P.weights (σ 0) : ℂ) * (1 - q ^ P.weights (σ 1)) * (1 - q ^ P.weights (σ 2))) := by
  obtain ⟨S, hpoly, heval⟩ := P.pole_polynomial_identity p hp ha τ hτ hN hd
  have hprod := Equiv.prod_comp σ (fun i => (1 - (X : Polynomial ℂ) ^ P.weights i))
  rw [← hprod, Fin.prod_univ_three] at hpoly
  have he := hypersurface_simple_weight_pole S (P.weights (σ 0)) (P.weights (σ 1))
    (P.weights (σ 2)) P.relationDegree N (P.weights_pos _) hN q hA hB hC hqN hq
    (by simpa only [mul_assoc] using hpoly)
  rw [heval q hqN hq] at he
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have hden := mul_ne_zero hN0 (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hq)))
  simpa only [mul_div_cancel_left₀ _ hden] using he

theorem RootHypersurfacePresentation.pair_weight_pole {a N : ℕ}
    (p : Fin 3 → ℕ) (hp : AdmissibleSignature p) (ha : 1 ≤ a)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) (P : RootHypersurfacePresentation p τ)
    (hN : 0 < N) (hd : ∀ i, p i ∣ N) (σ : Equiv.Perm (Fin 3))
    (q : ℂ) (hqN : q ^ N = 1) (hq : q ≠ 1)
    (hA : q ^ P.weights (σ 0) = 1) (hB : q ^ P.weights (σ 1) = 1)
    (hC : q ^ P.weights (σ 2) ≠ 1) (hh : q ^ P.relationDegree = 1) :
    (∑ i, if q ^ p i = 1 then 1 / ((p i : ℂ) * (1 - q ^ (-(a : ℤ)))) else 0) =
      (P.relationDegree : ℂ) /
        ((P.weights (σ 0) : ℂ) * P.weights (σ 1) * (1 - q ^ P.weights (σ 2))) := by
  obtain ⟨S, hpoly, heval⟩ := P.pole_polynomial_identity p hp ha τ hτ hN hd
  have hprod := Equiv.prod_comp σ (fun i => (1 - (X : Polynomial ℂ) ^ P.weights i))
  rw [← hprod, Fin.prod_univ_three] at hpoly
  have he := hypersurface_pair_weight_pole S (P.weights (σ 0)) (P.weights (σ 1))
    (P.weights (σ 2)) P.relationDegree N (P.weights_pos _) (P.weights_pos _) hN
    q hA hB hC hh hqN hq (by simpa only [mul_assoc] using hpoly)
  rw [heval q hqN hq] at he
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have hden := mul_ne_zero hN0 (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hq)))
  simpa only [mul_div_cancel_left₀ _ hden] using he

end CanonicalRoots
