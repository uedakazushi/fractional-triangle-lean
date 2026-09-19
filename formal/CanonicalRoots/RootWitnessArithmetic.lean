import CanonicalRoots.Payload
import CanonicalRoots.RootArithmetic

namespace CanonicalRoots

/-- The finite residue search used by the JSON root witness. -/
def rootWitnessResidue (a : ℕ) (q : ℤ) : ℕ :=
  ((List.range q.toNat).find? fun (s : ℕ) => ((a : ℤ) * s + 1) % q = 0).getD 0

def rootWitnessResidues (a : ℕ) (ps : List ℤ) : List ℕ := ps.map (rootWitnessResidue a)

def rootWitnessCarries (a : ℕ) (ps : List ℤ) : List ℤ :=
  (ps.zip (rootWitnessResidues a ps)).map fun (q,s) => ((a : ℤ) * s + 1) / q

def rootWitnessCoefficient (a : ℕ) (ps : List ℤ) : ℤ :=
  (1 - (rootWitnessCarries a ps).sum) / (a : ℤ)

theorem rootWitnessJson_arithmetic (a : ℕ) (ps : List ℤ) :
    rootWitnessJson a ps = Lean.Json.mkObj
      [("c_coefficient", jsonInt (rootWitnessCoefficient a ps)),
       ("residues", .arr ((rootWitnessResidues a ps).map jsonNat).toArray),
       ("signature_order", jsonInts ps)] := rfl

theorem rootWitnessResidue_spec (a : ℕ) (q : ℤ)
    (hex : ∃ s : ℕ, s < q.toNat ∧ ((a : ℤ) * s + 1) % q = 0) :
    rootWitnessResidue a q < q.toNat ∧
      ((a : ℤ) * rootWitnessResidue a q + 1) % q = 0 := by
  unfold rootWitnessResidue
  cases h : (List.range q.toNat).find? (fun (s : ℕ) => ((a : ℤ) * s + 1) % q = 0) with
  | none =>
    obtain ⟨s,hs,hm⟩ := hex
    have hn := List.find?_eq_none.mp h s (List.mem_range.mpr hs)
    simp [hm] at hn
  | some s =>
    have hs := List.mem_of_find?_eq_some h
    have hm := List.find?_some h
    simpa using And.intro (List.mem_range.mp hs) hm

/-- Coprimality makes the searched bounded residue equal to every bounded solution. -/
theorem rootWitnessResidue_eq (a p : ℕ) (hp : 0 < p) (e : ℤ)
    (he : 0 ≤ e ∧ e < p) (hc : IsCoprime (a : ℤ) (p : ℤ))
    (hm : ((a : ℤ) * e + 1) % p = 0) :
    (rootWitnessResidue a (p : ℤ) : ℤ) = e := by
  obtain ⟨hs,hr⟩ := rootWitnessResidue_spec a (p : ℤ) (by
    refine ⟨e.toNat,?_,?_⟩
    · simpa using (Int.toNat_lt_toNat (by exact_mod_cast hp : (0 : ℤ) < p)).mpr he.2
    · simpa [Int.toNat_of_nonneg he.1] using hm)
  have hd : (p : ℤ) ∣ (a : ℤ) * ((rootWitnessResidue a (p : ℤ) : ℤ) - e) := by
    have hsub := dvd_sub (Int.dvd_of_emod_eq_zero hr) (Int.dvd_of_emod_eq_zero hm)
    convert hsub using 1 <;> ring
  obtain ⟨k,hk⟩ := hc.symm.dvd_of_dvd_mul_left hd
  apply bounded_residue_unique (p : ℤ) _ e k (by exact_mod_cast hp)
    ⟨by positivity, by exact_mod_cast hs⟩ he hk

end CanonicalRoots
