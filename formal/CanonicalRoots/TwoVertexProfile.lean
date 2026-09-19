import CanonicalRoots.TwoVertexCoordinateData
import CanonicalRoots.TargetCoxScaleCriterion

noncomputable section
namespace CanonicalRoots

theorem reciprocal_pair_scale (B U e S κ : ℕ) (hB : 0 < B) (hU : 0 < U) (he : 0 < e)
    (hc : (e : ℚ) / B = (U : ℚ)⁻¹) (hS : S * e = κ * B) : S = κ * U := by
  have hB0 : (B : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hB
  have hU0 : (U : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hU
  have hprod : e * U = B := by
    have hrat := (div_eq_div_iff hB0 hU0).mp (by simpa only [one_div] using hc : (e : ℚ) / B = 1 / U)
    norm_num only [one_mul] at hrat
    exact_mod_cast hrat
  apply Nat.eq_of_mul_eq_mul_left he
  calc
    e * S = S * e := by ring
    _ = κ * B := hS
    _ = e * (κ * U) := by rw [← hprod]; ring

theorem Target.reciprocal_profile_of_two_vertex_data {a : ℕ} (t : Target 3 a)
    (σ : Equiv.Perm (Fin 3)) (U : ℕ) (c : ℚ)
    (hA : 2 ≤ t.presentation.weights (σ 0)) (hB : 2 ≤ t.presentation.weights (σ 1))
    (hdata : coordinateMultiplicity
      ![t.presentation.weights (σ 0), t.presentation.weights (σ 1), t.presentation.weights (σ 2)]
        t.presentation.relationDegree =
      weightedOrderAtom (t.presentation.weights (σ 0)) (t.presentation.weights (σ 0) : ℚ)⁻¹ +
      weightedOrderAtom (t.presentation.weights (σ 1)) (t.presentation.weights (σ 1) : ℚ)⁻¹ + weightedOrderAtom U c) :
    2 ≤ U ∧ c = (U : ℚ)⁻¹ ∧
      multipleSumLinear 1 (coordinateMultiplicity t.presentation.weights t.presentation.relationDegree) =
        1 / (t.presentation.weights (σ 0) : ℚ) + 1 / (t.presentation.weights (σ 1) : ℚ) + 1 / (U : ℚ) := by
  have htup : ![t.presentation.weights (σ 0), t.presentation.weights (σ 1), t.presentation.weights (σ 2)] =
      t.presentation.weights ∘ σ := by funext i; fin_cases i <;> rfl
  have hcoord : coordinateMultiplicity
      ![t.presentation.weights (σ 0), t.presentation.weights (σ 1), t.presentation.weights (σ 2)]
        t.presentation.relationDegree =
      coordinateMultiplicity t.presentation.weights t.presentation.relationDegree := by
    rw [htup, coordinateMultiplicity_reindex]
  have hmass := (t.ternary_permuted_coordinate_constraints σ).2.2.1
  rw [hdata] at hmass
  obtain ⟨hU, hc⟩ := two_vertex_mass_recovers_atom _ _ U c hA hB hmass
  refine ⟨hU, hc, ?_⟩
  rw [← hcoord, hdata, hc]
  simp [weightedOrderAtom, hA, hB, hU, map_add, multipleSumLinear_single]

end CanonicalRoots
