import CanonicalRoots.FermatCompletedBranch
import CanonicalRoots.TwoCoordinatePoints

noncomputable section
namespace CanonicalRoots
open MvPolynomial

variable {n : ℕ} (p : Fin (n + 1) → ℕ) (v : Fin (n + 1) → ℂ)

def fermatTailPoint : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ := aeval (fun i => v i.succ)

abbrev FermatTailCompletion := AdicCompletion (RingHom.ker (fermatTailPoint v).toRingHom)
  (MvPolynomial (Fin n) ℂ)

variable (hp : 0 < p 0) (hv : ∑ i, v i ^ p i = 0) (hv0 : v 0 ≠ 0)

include hp hv hv0 in
theorem fermat_tail_branch_exists :
    ∃ u : FermatTailCompletion v,
      u ^ p 0 + algebraMap (MvPolynomial (Fin n) ℂ) (FermatTailCompletion v)
        (fermat (fun i => p i.succ)) = 0 ∧
      u - algebraMap ℂ (FermatTailCompletion v) (v 0) ∈
        (RingHom.ker (fermatTailPoint v).toRingHom).map
          (algebraMap (MvPolynomial (Fin n) ℂ) (FermatTailCompletion v)) := by
  apply completed_power_branch_exists (fermatTailPoint v) (p 0) hp
    (fermat (fun i => p i.succ)) (v 0) hv0
  simpa only [fermatTailPoint, fermat, map_sum, map_pow, aeval_X, Fin.sum_univ_succ] using hv

def fermatCompletedBranch : FermatTailCompletion v :=
  (fermat_tail_branch_exists p v hp hv hv0).choose

theorem fermatCompletedBranch_equation :
    fermatCompletedBranch p v hp hv hv0 ^ p 0 +
      algebraMap (MvPolynomial (Fin n) ℂ) (FermatTailCompletion v)
        (fermat (fun i => p i.succ)) = 0 :=
  (fermat_tail_branch_exists p v hp hv hv0).choose_spec.1

theorem fermatCompletedBranch_residue :
    fermatCompletedBranch p v hp hv hv0 - algebraMap ℂ (FermatTailCompletion v) (v 0) ∈
      (RingHom.ker (fermatTailPoint v).toRingHom).map
        (algebraMap (MvPolynomial (Fin n) ℂ) (FermatTailCompletion v)) :=
  (fermat_tail_branch_exists p v hp hv hv0).choose_spec.2

def fermatCompletedCoordinates : Fin (n + 1) → FermatTailCompletion v :=
  Fin.cases (fermatCompletedBranch p v hp hv hv0)
    (fun i => algebraMap (MvPolynomial (Fin n) ℂ) (FermatTailCompletion v) (X i))

theorem fermatCompletedCoordinates_relation :
    ∑ i, fermatCompletedCoordinates p v hp hv hv0 i ^ p i = 0 := by
  simpa only [fermatCompletedCoordinates, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
    fermat, map_sum, map_pow] using fermatCompletedBranch_equation p v hp hv hv0

/-- A formal chart map from the original Fermat quotient into the actual completion
of the remaining polynomial coordinates at the original point. -/
def fermatFormalChart : AmbientRing p →ₐ[ℂ] FermatTailCompletion v :=
  Ideal.Quotient.liftₐ (fermatIdeal p) (aeval (fermatCompletedCoordinates p v hp hv hv0)) (by
    change Ideal.span {fermat p} ≤ RingHom.ker (aeval (fermatCompletedCoordinates p v hp hv hv0)).toRingHom
    apply Ideal.span_le.mpr
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    change aeval (fermatCompletedCoordinates p v hp hv hv0) (fermat p) = 0
    simpa only [fermat, map_sum, map_pow, aeval_X] using
      fermatCompletedCoordinates_relation p v hp hv hv0)

@[simp] theorem fermatFormalChart_X_zero :
    fermatFormalChart p v hp hv hv0 (ambientQuotient p (X 0)) = fermatCompletedBranch p v hp hv hv0 :=
  aeval_X _ _

@[simp] theorem fermatFormalChart_X_succ (i : Fin n) :
    fermatFormalChart p v hp hv hv0 (ambientQuotient p (X i.succ)) =
      algebraMap (MvPolynomial (Fin n) ℂ) (FermatTailCompletion v) (X i) := aeval_X _ _

end CanonicalRoots
