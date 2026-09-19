import CanonicalRoots.CoxIdentities

namespace CanonicalRoots.Cox

/-- Denominator estimate for the Fermat family. -/
theorem fermat_denominator (x y : ℤ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hne : x ≠ 2 ∨ y ≠ 2) :
    1 ≤ x*y-x-y ∧ x*y ≤ 6*(x*y-x-y) := by
  rcases eq_or_lt_of_le hx with h | h
  · subst x
    have hy3 : 3 ≤ y := by omega
    constructor <;> nlinarith
  · have hx3 : 3 ≤ x := by omega
    rcases eq_or_lt_of_le hy with h | h
    · subst y
      constructor <;> nlinarith
    · have hy3 : 3 ≤ y := by omega
      have hxy := mul_nonneg (show 0 ≤ x-3 by omega) (show 0 ≤ y-3 by omega)
      constructor <;> nlinarith

/-- Each selected coordinate of a Fermat solution is bounded. -/
theorem fermat_coordinate_bound (x y z d : ℤ)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z) (hd : 1 ≤ d)
    (he : x*y*z - (y*z + x*z + x*y) = d) : z ≤ d+6 := by
  have hne : x ≠ 2 ∨ y ≠ 2 := by
    by_contra h
    push Not at h
    rcases h with ⟨rfl, rfl⟩
    nlinarith
  obtain ⟨hden, hratio⟩ := fermat_denominator x y hx hy hne
  have hdprod := mul_nonneg (show 0 ≤ d by omega) (show 0 ≤ (x*y-x-y)-1 by omega)
  have hfact : z * (x*y-x-y) = d+x*y := by nlinarith [he]
  nlinarith

/-- Uniform factor bound, with no coprimality assumptions. -/
theorem product_sum_bound (A B t c : ℤ)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (ht : 1 ≤ t) (hc : 1 ≤ c)
    (he : t*A*B = A+B+c) : A ≤ c+2 ∧ B ≤ c+2 ∧ t ≤ c+2 := by
  have hab : 1 ≤ A*B := by nlinarith
  have htab : A*B ≤ t*A*B := by nlinarith [mul_nonneg (show 0 ≤ t-1 by omega) (show 0 ≤ A*B by omega)]
  have bound_first : ∀ U V : ℤ, 1 ≤ U → 1 ≤ V → U*V ≤ U+V+c →
      t*U*V = U+V+c → U ≤ c+2 := by
    intro U V hU hV hUV hEq
    rcases eq_or_lt_of_le hV with hv | hv
    · subst V
      have ht2 : 2 ≤ t := by
        by_contra h
        have : t = 1 := by omega
        subst t
        nlinarith
      nlinarith [mul_nonneg (show 0 ≤ t-2 by omega) (show 0 ≤ U by omega)]
    · have hv2 : 2 ≤ V := by omega
      nlinarith [mul_nonneg (show 0 ≤ U-1 by omega) (show 0 ≤ V-2 by omega)]
  have h1 := bound_first A B hA hB (by omega) he
  have h2 := bound_first B A hB hA (by nlinarith [htab]) (by nlinarith [he])
  have hAmul : A ≤ A*B := by nlinarith [mul_nonneg (show 0 ≤ A by omega) (show 0 ≤ B-1 by omega)]
  have hBmul : B ≤ A*B := by nlinarith [mul_nonneg (show 0 ≤ B by omega) (show 0 ≤ A-1 by omega)]
  have hcmul : c ≤ c*(A*B) := by nlinarith [mul_nonneg (show 0 ≤ c by omega) (show 0 ≤ A*B-1 by omega)]
  exact ⟨h1,h2,by nlinarith⟩

/-- The prescribed a+6 box covers all five arithmetic families, for every a. -/
theorem exponent_bound (k : Kind) (x y z d : ℤ)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z) (hd : 1 ≤ d)
    (he : defect k x y z = d) : x ≤ d+6 ∧ y ≤ d+6 ∧ z ≤ d+6 := by
  have hx1 : 1 ≤ x-1 := by omega
  have hy1 : 1 ≤ y-1 := by omega
  have hz1 : 1 ≤ z-1 := by omega
  cases k with
  | I =>
    simp [defect, degree, weights, Fin.sum_univ_succ] at he
    exact ⟨fermat_coordinate_bound y z x d hy hz hx hd (by nlinarith [he]),
      fermat_coordinate_bound x z y d hx hz hy hd (by nlinarith [he]),
      fermat_coordinate_bound x y z d hx hy hz hd (by nlinarith [he])⟩
  | II =>
    simp [defect, degree, weights, Fin.sum_univ_succ] at he
    have h := product_sum_bound (x-1) (y-1) (z-1) (d+1) hx1 hy1 hz1 (by omega)
      (by nlinarith [he])
    omega
  | III =>
    simp [defect, degree, weights, Fin.sum_univ_succ] at he
    have h := product_sum_bound (x-1) (y-1) (z-1) d hx1 hy1 hz1 hd
      (by nlinarith [he])
    omega
  | IV =>
    simp [defect, degree, weights, Fin.sum_univ_succ] at he
    have ht : 1 ≤ (z-1)*(x-1)-1 := by
      have hprod : 1 ≤ (z-1)*(x-1) := by nlinarith
      by_contra h
      have : (z-1)*(x-1) = 1 := by omega
      nlinarith [he]
    have hEq : (y-1)*((z-1)*(x-1)-1) = d+1 := by nlinarith [he]
    have hB : y-1 ≤ d+1 := by nlinarith
    have hT : (z-1)*(x-1)-1 ≤ d+1 := by nlinarith
    have hX : x-1 ≤ (z-1)*(x-1) := by nlinarith
    have hZ : z-1 ≤ (z-1)*(x-1) := by nlinarith
    exact ⟨by omega,by omega,by omega⟩
  | V =>
    simp [defect, degree, weights, Fin.sum_univ_succ] at he
    have hEq : (x-1)*(y-1)*(z-1) = d+1 := by nlinarith [he]
    have hXY : 1 ≤ (x-1)*(y-1) := by nlinarith
    have hprod : (x-1)*(y-1) ≤ d+1 := by nlinarith
    have hX : x-1 ≤ (x-1)*(y-1) := by nlinarith
    have hY : y-1 ≤ (x-1)*(y-1) := by nlinarith
    have hZ : z-1 ≤ d+1 := by nlinarith
    exact ⟨by omega,by omega,by omega⟩

end CanonicalRoots.Cox
