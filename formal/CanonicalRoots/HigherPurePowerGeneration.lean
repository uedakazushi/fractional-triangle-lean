import CanonicalRoots.CoprimeRootPurePowers
import CanonicalRoots.RootPointFibers
import CanonicalRoots.FourCoordinatePowerFiber
import CanonicalRoots.TwoCoordinatePoints

noncomputable section
namespace CanonicalRoots

variable {n a : ℕ} (p : Fin (n + 1) → ℕ) (hp : AdmissibleSignature p)
  (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
  (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j)))

include hp ha hτ hcop in
/-- In at least four coordinates, generation by the pure `u`th powers forces
`u=1`. The proof uses actual finite-quotient fibers, not a formal division premise. -/
theorem higher_scale_eq_one_of_pure_power_generation (hn : 3 ≤ n)
    (hgen : Algebra.adjoin ℂ (Set.range (coprimeRootPurePower p hp ha τ hτ hcop)) = ⊤) :
    canonicalRootScale p a = 1 := by
  have hu := canonicalRootScale_pos p hp ha τ hτ
  by_contra hne
  obtain ⟨v, w, hv, hw, hpow, hnot⟩ := fourCoordinatePowerFiber_exists p
    (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) hn (by omega)
    (canonicalRootScale_coprime_coordinate p hp ha τ hτ hcop)
  let z := fermatPoint p v hv
  let z' := fermatPoint p w hw
  have he : rootPoint p τ z = rootPoint p τ z' := by
    apply AlgHom.ext_of_adjoin_eq_top hgen
    rintro _ ⟨i, rfl⟩
    simp only [coprimeRootPurePower_point, z, z', fermatPoint_X]
    exact hpow i
  obtain ⟨ρ, hρ⟩ := rootPoint_eq_powers_proportional p hp ha τ hτ z z' he
  apply hnot
  exact ⟨ρ, fun i => by simpa only [z, z', fermatPoint_X] using hρ i⟩

end CanonicalRoots
