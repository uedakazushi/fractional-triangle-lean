import CanonicalRoots.RootIsolatedCotangent
import CanonicalRoots.RootNonregularStratum

noncomputable section
namespace CanonicalRoots

variable {n a : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
  (hp : AdmissibleSignature p) (ha : 1 ≤ a) (hτ : IsCanonicalRoot p a τ)

include hp ha hτ in
/-- Isolation of the actual root hypersurface excludes a common factor of any
two exponents other than the coordinate eliminated by the current chart. -/
theorem RootHypersurfacePresentation.tail_pairwise_coprime
    (H : RootHypersurfacePresentation p τ) (hn : 3 ≤ n) :
    Pairwise (fun i j : Fin n => Nat.Coprime (p i.succ) (p j.succ)) := by
  intro i j hij
  by_contra hcop
  have hs : 2 ≤ Nat.gcd (p i.succ) (p j.succ) := by
    have hpos := Nat.gcd_pos_of_pos_left (p j.succ)
      (lt_of_lt_of_le (by decide : 0 < 2) (hp.1 i.succ))
    change Nat.gcd (p i.succ) (p j.succ) ≠ 1 at hcop
    omega
  obtain ⟨z, hi, hj, hz⟩ := twoCoordinatePoint_exists p
    (fun k => lt_of_lt_of_le (by decide) (hp.1 k)) hn i.succ j.succ (by simpa using hij)
  let v := fun l => z (ambientQuotient p (MvPolynomial.X l))
  have hv := fermatPoint_coordinates_relation p z
  have hlo := rootTwoCoordinate_cotangent_lowerBound p τ hp ha hτ v hv i j hij hi hj hz hs
  have hnon := (rootTwoCoordinate_nonorigin_nonregular p τ hp ha hτ v hv i j hij hi hj hz hs).1
  have hhi := H.nonorigin_local_cotangent_lt p τ hp ha hτ
    (rootPoint p τ (fermatPoint p v hv)) hnon
  omega

theorem Target.tail_pairwise_coprime (t : Target (n + 1) a) (hn : 3 ≤ n) :
    Pairwise (fun i j : Fin n => Nat.Coprime (t.signature i.succ) (t.signature j.succ)) :=
  t.presentation.tail_pairwise_coprime t.signature t.tau t.admissible t.parameter_input
    t.root_equation hn

end CanonicalRoots
