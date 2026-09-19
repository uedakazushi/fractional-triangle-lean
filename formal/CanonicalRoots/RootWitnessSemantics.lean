import CanonicalRoots.RootWitnessArithmetic

noncomputable section
namespace CanonicalRoots

theorem rootWitnessCarries_ofFn {n : ℕ} (a : ℕ) (p : Fin n → ℤ) :
    rootWitnessCarries a (List.ofFn p) =
      List.ofFn (fun i => ((a : ℤ) * rootWitnessResidue a (p i) + 1) / p i) := by
  simp [rootWitnessCarries, rootWitnessResidues, List.ofFn_eq_map, List.map_map,
    List.zip_map']

/-- Interpret exactly the integer coefficient and residues emitted in the payload. -/
def rootWitnessDegree {n : ℕ} (a : ℕ) (p : Fin n → ℕ) : DegreeGroup p :=
  normalDegree p (rootWitnessCoefficient a (List.ofFn (fun i => (p i : ℤ))))
    (fun i => (rootWitnessResidue a (p i : ℤ) : ℤ))

/-- The executable finite search recovers the actual torsion-retaining root, not just its rational degree. -/
theorem rootWitnessDegree_eq {n a : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    rootWitnessDegree a p = τ := by
  obtain ⟨b,e,he,hτe⟩ := degree_normal_exists p hp τ
  obtain ⟨q,hb,hq⟩ := (canonicalRoot_normal_iff p b e).mp (hτe ▸ hτ)
  have hr (i : Fin n) : (rootWitnessResidue a (p i : ℤ) : ℤ) = e i := by
    apply rootWitnessResidue_eq a (p i) (hp i) (e i) (he i)
      (canonicalRoot_coprime p hp τ hτ i)
    rw [hq i]
    simp
  have hc : rootWitnessCarries a (List.ofFn (fun i => (p i : ℤ))) = List.ofFn q := by
    rw [rootWitnessCarries_ofFn]
    congr 1
    funext i
    rw [hr i, hq i, Int.mul_ediv_cancel_left _ (by exact_mod_cast (ne_of_gt (hp i)))]
  have hb' : rootWitnessCoefficient a (List.ofFn (fun i => (p i : ℤ))) = b := by
    unfold rootWitnessCoefficient
    rw [hc, List.sum_ofFn, show 1 - ∑ i, q i = (a : ℤ) * b from by omega,
      Int.mul_ediv_cancel_left _ (by exact_mod_cast (by omega : a ≠ 0))]
  unfold rootWitnessDegree
  rw [hb', show (fun i => (rootWitnessResidue a (p i : ℤ) : ℤ)) = e from funext hr]
  exact hτe.symm

theorem rootWitnessDegree_isCanonicalRoot {n a : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (ha : 1 ≤ a) (hex : ∃ τ, IsCanonicalRoot p a τ) :
    IsCanonicalRoot p a (rootWitnessDegree a p) := by
  obtain ⟨τ,hτ⟩ := hex
  rw [rootWitnessDegree_eq p hp ha τ hτ]
  exact hτ

end CanonicalRoots
