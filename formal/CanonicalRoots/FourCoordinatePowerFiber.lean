import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

noncomputable section
namespace CanonicalRoots

/-- Coprime powering permutes the actual complex roots of unity. -/
theorem complex_coprime_power_lift {u q : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u q)
    (ζ : ℂ) (hζ : ζ ^ u = 1) : ∃ β : ℂ, β ^ u = 1 ∧ β ^ q = ζ := by
  let : NeZero u := ⟨ne_of_gt hu⟩
  let z : rootsOfUnity u ℂ := rootsOfUnity.mkOfPowEq ζ hζ
  have hc : (Nat.card (rootsOfUnity u ℂ)).Coprime q := by
    rw [Complex.card_rootsOfUnity]
    exact hcop
  obtain ⟨b, hb⟩ := (powCoprime (G := rootsOfUnity u ℂ) hc).surjective z
  change b ^ q = z at hb
  refine ⟨(b.val : ℂ), ?_, ?_⟩
  · exact congrArg (fun η : ℂˣ => (η : ℂ)) ((mem_rootsOfUnity _ _).mp b.property)
  · have he := congrArg (fun η : rootsOfUnity u ℂ => ((η : ℂˣ) : ℂ)) hb
    simpa only [rootsOfUnity.coe_pow, z, rootsOfUnity.coe_mkOfPowEq] using he

/-- In at least four coordinates, coprime coordinate powers of order greater
than one identify Fermat points whose Fermat-power vectors are not proportional. -/
theorem fourCoordinatePowerFiber_exists {n u : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : ∀ i, 0 < p i) (hn : 3 ≤ n) (hu : 1 < u)
    (hcop : ∀ i, Nat.Coprime u (p i)) :
    ∃ v w : Fin (n + 1) → ℂ,
      (∑ i, v i ^ p i = 0) ∧ (∑ i, w i ^ p i = 0) ∧
      (∀ i, v i ^ u = w i ^ u) ∧
      ¬∃ ρ : ℂ, ∀ i, v i ^ p i = ρ * w i ^ p i := by
  classical
  let i0 : Fin (n + 1) := ⟨0, by omega⟩
  let i1 : Fin (n + 1) := ⟨1, by omega⟩
  let i2 : Fin (n + 1) := ⟨2, by omega⟩
  let i3 : Fin (n + 1) := ⟨3, by omega⟩
  let Y : Fin (n + 1) → ℂ := fun i =>
    (if i = i0 then 1 else 0) - (if i = i1 then 1 else 0) +
      (if i = i2 then 1 else 0) - (if i = i3 then 1 else 0)
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / u)
  have hprim := Complex.isPrimitiveRoot_exp u (by omega : u ≠ 0)
  have hζ : ζ ^ u = 1 := hprim.pow_eq_one
  have hζne : ζ ≠ 1 := by
    intro he
    have hd := hprim.dvd_of_pow_eq_one 1 (by simpa only [pow_one] using he)
    have := Nat.dvd_one.mp hd
    omega
  choose v hv using fun i => IsAlgClosed.exists_pow_nat_eq (Y i) (hp i)
  choose β hβu hβp using fun i => complex_coprime_power_lift (by omega : 0 < u) (hcop i) ζ hζ
  let w : Fin (n + 1) → ℂ := fun i => if i = i0 ∨ i = i1 then β i * v i else v i
  have hw (i : Fin (n + 1)) : w i ^ p i =
      (if i = i0 then ζ else 0) - (if i = i1 then ζ else 0) +
        (if i = i2 then 1 else 0) - (if i = i3 then 1 else 0) := by
    by_cases h0 : i = i0
    · subst i
      simp [w, mul_pow, hβp, hv, Y, i0, i1, i2, i3]
    by_cases h1 : i = i1
    · subst i
      simp [w, mul_pow, hβp, hv, Y, i0, i1, i2, i3]
    by_cases h2 : i = i2
    · subst i
      simp [w, hv, Y, i0, i1, i2, i3]
    by_cases h3 : i = i3
    · subst i
      simp [w, hv, Y, i0, i1, i2, i3]
    simp [w, h0, h1, h2, h3, hv, Y]
  refine ⟨v, w, ?_, ?_, ?_, ?_⟩
  · simp_rw [hv]
    simp [Y, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  · simp_rw [hw]
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  · intro i
    simp only [w]
    split_ifs
    · rw [mul_pow, hβu, one_mul]
    · rfl
  · rintro ⟨ρ, hρ⟩
    have he2 := hρ i2
    have he0 := hρ i0
    simp only [hv, hw] at he2 he0
    norm_num [Y, i0, i1, i2, i3] at he2 he0
    rw [← he2, one_mul] at he0
    exact hζne he0.symm

end CanonicalRoots
