import CanonicalRoots.DegreeUniversal

noncomputable section
namespace CanonicalRoots

variable {n : ℕ} (p : Fin n → ℕ) (e : Equiv.Perm (Fin n))

/-- Permuting coordinates preserves the whole degree group, including its torsion. -/
def degreeReindex : DegreeGroup (fun i => p (e i)) ≃+ DegreeGroup p := by
  let f := degreeLift (fun i => p (e i)) (fun i => xDegree p (e i)) (cDegree p)
    (fun i => degree_relation p (e i))
  let g := degreeLift p (fun i => xDegree (fun j => p (e j)) (e.symm i))
    (cDegree (fun j => p (e j))) (fun i => by
      simpa only [e.apply_symm_apply] using degree_relation (fun j => p (e j)) (e.symm i))
  refine { f with invFun := g, left_inv := ?_, right_inv := ?_ }
  · have h : g.comp f = AddMonoidHom.id _ := by
      apply degreeHom_ext
      · simp [f, g]
      · intro i; simp [f, g]
    exact fun x => DFunLike.congr_fun h x
  · have h : f.comp g = AddMonoidHom.id _ := by
      apply degreeHom_ext
      · simp [f, g]
      · intro i; simp [f, g]
    exact fun x => DFunLike.congr_fun h x

@[simp] theorem degreeReindex_c :
    degreeReindex p e (cDegree (fun i => p (e i))) = cDegree p :=
  degreeLift_c (fun i => p (e i)) (fun i => xDegree p (e i)) (cDegree p)
    (fun i => degree_relation p (e i))

@[simp] theorem degreeReindex_x (i : Fin n) :
    degreeReindex p e (xDegree (fun j => p (e j)) i) = xDegree p (e i) :=
  degreeLift_x (fun i => p (e i)) (fun i => xDegree p (e i)) (cDegree p)
    (fun i => degree_relation p (e i)) i

@[simp] theorem degreeReindex_omega :
    degreeReindex p e (omegaDegree (fun i => p (e i))) = omegaDegree p := by
  simp only [omegaDegree, map_sub, map_sum, degreeReindex_c, degreeReindex_x]
  rw [Equiv.sum_comp e (xDegree p)]

theorem admissibleSignature_reindex (hp : AdmissibleSignature p) :
    AdmissibleSignature (fun i => p (e i)) := by
  refine ⟨fun i => hp.1 (e i), ?_⟩
  rw [Equiv.sum_comp e (fun i => (1 : ℚ) / p i)]
  exact hp.2

theorem canonicalRoot_reindex {a : ℕ} (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    IsCanonicalRoot (fun i => p (e i)) a ((degreeReindex p e).symm τ) := by
  apply (degreeReindex p e).injective
  change degreeReindex p e (a • (degreeReindex p e).symm τ) =
    degreeReindex p e (omegaDegree (fun i => p (e i)))
  rw [map_nsmul, AddEquiv.apply_symm_apply, degreeReindex_omega]
  exact hτ

end CanonicalRoots
