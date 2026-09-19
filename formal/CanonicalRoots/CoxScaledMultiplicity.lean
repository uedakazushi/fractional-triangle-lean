import CanonicalRoots.CoxWeightNormalization

namespace CanonicalRoots

/-- A common factor in a ternary multiplicity identity appears as kappa-1 in
its normalized defect. This also covers repeated signature entries. -/
theorem scaled_triple_multiplicity_defect (A B C p q r a h κ : ℚ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hκ : κ ≠ 0)
    (he : (κ * a) * (κ * h) * ((κ * p) * (κ * q) * (κ * r)) =
      ((κ * A) * (κ * B) * (κ * C)) *
        (((κ * p) * (κ * q) * (κ * r)) -
          ((κ * q) * (κ * r) + (κ * p) * (κ * r) + (κ * p) * (κ * q)))) :
    a * (h / (A * B * C)) - 1 + (1 / p + 1 / q + 1 / r) = κ - 1 := by
  have he' : κ ^ 5 * (a * h * (p * q * r) - A * B * C *
      (κ * (p * q * r) - (q * r + p * r + p * q))) = 0 := by
    linear_combination he
  have hz : a * h * (p * q * r) - A * B * C *
      (κ * (p * q * r) - (q * r + p * r + p * q)) = 0 :=
    (mul_eq_zero.mp he').resolve_left (pow_ne_zero 5 hκ)
  field_simp
  nlinarith [hz]

namespace Cox

/-- Reuse the universal Cox multiplicity identity after scaling both weights
and the three signature orders. -/
theorem scaled_signature_defect (kind : Kind) (α β γ : ℤ)
    (w p : Fin 3 → ℚ) (a h κ : ℚ) (hw0 : ∀ i, w i ≠ 0) (hp0 : ∀ i, p i ≠ 0)
    (hκ : κ ≠ 0)
    (hw : ∀ i, (weights kind α β γ i : ℚ) = κ * w i)
    (hp : ∀ i, (signature kind α β γ i : ℚ) = κ * p i)
    (hd : (degree kind α β γ : ℚ) = κ * h)
    (ha : (defect kind α β γ : ℚ) = κ * a) :
    a * (h / ∏ i, w i) - 1 + ∑ i, 1 / p i = κ - 1 := by
  have he := congrArg (fun z : ℤ => (z : ℚ)) (multiplicity kind α β γ)
  push_cast at he
  simp only [Fin.prod_univ_three, hw, hp, hd, ha] at he
  simpa only [Fin.prod_univ_three, Fin.sum_univ_three] using
    scaled_triple_multiplicity_defect (w 0) (w 1) (w 2) (p 0) (p 1) (p 2) a h κ
      (hw0 0) (hw0 1) (hw0 2) (hp0 0) (hp0 1) (hp0 2) hκ he

end Cox
end CanonicalRoots
