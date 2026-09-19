import CanonicalRoots.BranchedTwoExclusion
import CanonicalRoots.NumericAxisWeights

noncomputable section
namespace CanonicalRoots

theorem branched_center_pure_forces_outside_pure (A B C h α γ : ℕ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hBh : B < h)
    (h0 : α * A + B = h) (h2 : γ * C + B = h) (hdB : B ∣ h)
    (hAC : Nat.Coprime A C)
    (hmass : orderMassLinear (coordinateMultiplicity ![A,B,C] h) = 3) :
    A ∣ h ∨ C ∣ h := by
  obtain ⟨q, hq⟩ := hdB
  have hq2 : 2 ≤ q := by nlinarith
  let e := q - 1
  have heq : q = e + 1 := by dsimp [e]; omega
  have he : 0 < e := by omega
  have hh : h = (e + 1) * B := by rw [hq, heq, mul_comm]
  have hEA : e * B = α * A := by nlinarith [hh, h0]
  have hEC : e * B = γ * C := by nlinarith [hh, h2]
  apply branchedOne_has_pure_vertex A B C e h hA hB hC he hh
  · rw [hEA]; exact dvd_mul_left _ _
  · rw [hEC]; exact dvd_mul_left _ _
  · exact hAC
  · exact hmass

theorem branchedTwo_outside_pure_vertex (A B C h a α β γ : ℕ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hBh : B < h)
    (hα : 2 ≤ α) (hβ : 2 ≤ β) (hγ : 2 ≤ γ)
    (h0 : α * A + B = h) (h1 : β * B + C = h) (h2 : γ * C + B = h)
    (hdef : h = a + (A + B + C)) (hAB : Nat.Coprime A B) (hAC : Nat.Coprime A C)
    (hmass : orderMassLinear (coordinateMultiplicity ![A,B,C] h) = 3)
    (hzero : (a : ℚ) * ((h : ℚ) / ((A : ℚ) * B * C)) - 1 +
      multipleSumLinear 1 (coordinateMultiplicity ![A,B,C] h) = 0) :
    A ∣ h ∨ C ∣ h := by
  rcases branchedTwo_has_pure_vertex A B C h a α β γ hA hB hC hα hβ hγ h0 h1 h2
      hdef hAB hAC hmass hzero with hd | hd | hd
  · exact Or.inl hd
  · exact branched_center_pure_forces_outside_pure A B C h α γ hA hB hC hBh h0 h2 hd hAC hmass
  · exact Or.inr hd

end CanonicalRoots
