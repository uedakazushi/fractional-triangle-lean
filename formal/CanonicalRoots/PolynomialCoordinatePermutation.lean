import CanonicalRoots.Target

noncomputable section
namespace CanonicalRoots
open MvPolynomial

theorem weightedHomogeneous_rename_perm {n h : ℕ} (e : Equiv.Perm (Fin n))
    (f : MvPolynomial (Fin n) ℂ) (w : Fin n → ℕ)
    (hf : IsWeightedHomogeneous (fun i => w (e i)) f h) :
    IsWeightedHomogeneous w (rename e f) h := by
  intro d hd
  obtain ⟨c, rfl⟩ := Finsupp.mapDomain_surjective e.surjective d
  have hc := hf (by simpa only [coeff_rename_mapDomain e e.injective] using hd)
  rw [Finsupp.weight_eq_sum,
    ← Equiv.sum_comp e (fun i => c.mapDomain e i • w i)]
  simpa only [Finsupp.mapDomain_apply_of_injective e.injective,
    Finsupp.weight_eq_sum] using hc

theorem noConstantOrLinear_rename_perm {n : ℕ} (e : Equiv.Perm (Fin n))
    (f : MvPolynomial (Fin n) ℂ) (hf : HasNoConstantOrLinear f) :
    HasNoConstantOrLinear (rename e f) := by
  constructor
  · simpa using (coeff_rename_mapDomain e e.injective f 0).trans hf.1
  · intro i
    simpa using (coeff_rename_mapDomain e e.injective f (Finsupp.single (e.symm i) 1)).trans
      (hf.2 (e.symm i))

theorem isolated_rename_perm {n : ℕ} (e : Equiv.Perm (Fin n))
    (f : MvPolynomial (Fin n) ℂ) (hf : IsolatedAtOrigin f) :
    IsolatedAtOrigin (rename e f) := by
  intro z
  constructor
  · intro hz
    have hzero : (z ∘ e) = 0 := (hf _).mp (fun i => by
      simpa only [pderiv_rename e.injective, eval_rename] using hz (e i))
    funext i
    simpa using congrFun hzero (e.symm i)
  · rintro rfl i
    have hz := (hf 0).mpr rfl (e.symm i)
    have he : i = e (e.symm i) := (e.apply_symm_apply i).symm
    conv_lhs => arg 2; arg 1; rw [he]
    rw [pderiv_rename e.injective, eval_rename]
    simpa using hz

end CanonicalRoots
