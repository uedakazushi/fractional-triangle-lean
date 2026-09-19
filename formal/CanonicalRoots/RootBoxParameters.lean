import CanonicalRoots.RootResidueClasses
import CanonicalRoots.FiniteSumFiber

noncomputable section
namespace CanonicalRoots

/-- One root residue modulo N, together with bounded quotient coordinates satisfying one congruence. -/
def RootBoxParameters {n : ℕ} (p : Fin (n + 1) → ℕ) (b : ℤ)
    (σ : Fin (n + 1) → ℤ) (u : ℕ) :=
  (m : Fin (signatureLcm p)) × BoundedSumFiber n u (rootCarry p b σ m)

section Root
variable {n a : ℕ} (p : Fin (n + 1) → ℕ) (hp : AdmissibleSignature p) (ha : 1 ≤ a)
  (b : ℤ) (σ : Fin (n + 1) → ℤ) (hroot : IsCanonicalRoot p a (normalDegree p b σ))
  (u : ℕ) (hN : signatureLcm p • normalDegree p b σ = u • cDegree p)

def rootBoxParameterMap (x : RootBoxParameters p b σ u) : RootBox p (normalDegree p b σ) u := by
  let hpos : ∀ i, 0 < p i := fun i => lt_of_lt_of_le (by decide) (hp.1 i)
  let q := (boxCoordinatesEquiv p hpos u).symm (x.2.val, rootResidueVector p hpos σ x.1)
  refine ⟨q, (box_mem_root_iff_integer p hp ha _ hroot u q).mpr ?_⟩
  obtain ⟨k, hk⟩ := x.2.property
  refine ⟨(x.1 : ℤ) + k * signatureLcm p, ?_⟩
  have hsum : (∑ i, (x.2.val i : ℤ)) = rootCarry p b σ x.1 + k * u := by
    change (∑ i, (x.2.val i : ℤ)) - rootCarry p b σ x.1 = (u : ℤ) * k at hk
    linarith
  change boxDegree p u ((boxCoordinatesEquiv p hpos u).symm _) = _
  rw [boxDegree_coordinates, hsum]
  simp only [rootResidueVector_cast]
  rw [normalDegree_add_c, ← rootDegree_normal]
  simp only [add_zsmul, mul_smul, natCast_zsmul, hN]

theorem rootBoxParameterMap_coordinates (x : RootBoxParameters p b σ u) :
    boxCoordinatesEquiv p (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) u
      (rootBoxParameterMap p hp ha b σ hroot u hN x).val =
    (x.2.val, rootResidueVector p (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) σ x.1) :=
  (boxCoordinatesEquiv p _ u).apply_symm_apply _

theorem rootBoxParameterMap_injective :
    Function.Injective (rootBoxParameterMap p hp ha b σ hroot u hN) := by
  intro x y he
  have hc := congrArg (fun q : RootBox p (normalDegree p b σ) u =>
    boxCoordinatesEquiv p (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) u q.val) he
  rw [rootBoxParameterMap_coordinates, rootBoxParameterMap_coordinates] at hc
  have hm : x.1 = y.1 := rootResidueVector_injective p
    (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) b σ hroot (congrArg Prod.snd hc)
  rcases x with ⟨m, d⟩
  rcases y with ⟨k, e⟩
  change m = k at hm
  subst k
  have hd : d = e := Subtype.ext (congrArg Prod.fst hc)
  subst e
  rfl

theorem rootBoxParameterMap_surjective :
    Function.Surjective (rootBoxParameterMap p hp ha b σ hroot u hN) := by
  intro q
  let hpos : ∀ i, 0 < p i := fun i => lt_of_lt_of_le (by decide) (hp.1 i)
  let c := boxCoordinatesEquiv p hpos u q.val
  obtain ⟨m, hm⟩ := q.property
  have he : normalDegree p (∑ i, (c.1 i : ℤ)) (fun i => (c.2 i : ℤ)) =
      normalDegree p (rootCarry p b σ m) (rootResidue p σ m) := by
    rw [← rootDegree_normal, ← boxDegree_coordinates p hpos u c]
    simpa only [c, Equiv.symm_apply_apply] using hm
  have hn := degree_normal_unique p hpos _ _ _ _
    (fun i => ⟨by positivity, by exact_mod_cast (c.2 i).isLt⟩)
    (rootResidue_bounded p hpos σ m) he
  have hperiod := rootCarry_residue_mod p hpos b σ (signatureLcm p) m (u : ℤ) hN
  let r : Fin (signatureLcm p) := ⟨m % signatureLcm p, Nat.mod_lt _ (signature_lcm_pos p hpos)⟩
  have hf : (u : ℤ) ∣ (∑ i, (c.1 i : ℤ)) - rootCarry p b σ r := by
    refine ⟨((m / signatureLcm p : ℕ) : ℤ), ?_⟩
    change _ - rootCarry p b σ (m % signatureLcm p) = _
    rw [hn.1, hperiod.1]
    ring
  let x : RootBoxParameters p b σ u := ⟨r, ⟨c.1, hf⟩⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  apply (boxCoordinatesEquiv p hpos u).injective
  rw [rootBoxParameterMap_coordinates]
  change (c.1, rootResidueVector p hpos σ r) = c
  refine Prod.ext ?_ ?_
  · rfl
  funext i
  apply Fin.ext
  have hi := congrFun (hn.2.trans hperiod.2) i
  have hr := rootResidueVector_cast p hpos σ r i
  exact_mod_cast (hr.trans hi.symm)

/-- A bijection with the actual finite root box, not a numerical replacement for its definition. -/
def rootBoxParametersEquiv : RootBoxParameters p b σ u ≃ RootBox p (normalDegree p b σ) u :=
  Equiv.ofBijective (rootBoxParameterMap p hp ha b σ hroot u hN)
    ⟨rootBoxParameterMap_injective p hp ha b σ hroot u hN,
      rootBoxParameterMap_surjective p hp ha b σ hroot u hN⟩

end Root
end CanonicalRoots
