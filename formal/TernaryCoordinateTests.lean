import CanonicalRoots.CoordinateSignatureConstraints

noncomputable section
open CanonicalRoots

-- A Fermat presentation: all signature data comes from pair gcd orders.
example : coordinateMultiplicity ![21,14,6] 42 =
    Finsupp.single 2 (1/2) + Finsupp.single 3 (1/3) + Finsupp.single 7 (1/7) := by
  ext r
  norm_num [coordinateMultiplicity, coordinateVertexCoefficient, weightedOrderAtom,
    Fin.sum_univ_three, Finsupp.single_apply]
  split_ifs <;> norm_num <;> omega

-- The determinant-48 Fermat equation has signature (3,3,4), including repetition.
example : coordinateMultiplicity ![12,8,3] 24 =
    Finsupp.single 3 (2/3) + Finsupp.single 4 (1/4) := by
  ext r
  norm_num [coordinateMultiplicity, coordinateVertexCoefficient, weightedOrderAtom,
    Fin.sum_univ_three, Finsupp.single_apply]
  split_ifs <;> norm_num <;> omega

-- These are actual Target consequences, with no model or orbit-signature premise.
example {a : ℕ} (t : Target 3 a) :
    orderMassLinear (coordinateMultiplicity t.presentation.weights t.presentation.relationDegree) = 3 :=
  t.coordinateMultiplicity_mass

example {a : ℕ} (t : Target 3 a) (r : ℕ) (hr : 0 < r) :
    (r : ℚ) * coordinateMultiplicity t.presentation.weights t.presentation.relationDegree r =
      (List.ofFn t.signature : Multiset ℕ).count r := t.coordinateMultiplicity_order_mul r hr

example {a : ℕ} (t : Target 3 a) :
    (a : ℚ) * ((t.presentation.relationDegree : ℚ) / ∏ i, (t.presentation.weights i : ℚ)) - 1 +
      multipleSumLinear 1 (coordinateMultiplicity t.presentation.weights t.presentation.relationDegree) = 0 :=
  t.coordinateMultiplicity_defect
