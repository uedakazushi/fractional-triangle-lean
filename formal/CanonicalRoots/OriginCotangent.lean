import CanonicalRoots.Target

noncomputable section
namespace CanonicalRoots
open MvPolynomial

abbrev polynomialOriginIdeal (n : ℕ) : Ideal (MvPolynomial (Fin n) ℂ) :=
  idealOfVars (Fin n) ℂ

theorem mem_polynomialOriginIdeal_iff {n : ℕ} (f : MvPolynomial (Fin n) ℂ) :
    f ∈ polynomialOriginIdeal n ↔ f.coeff 0 = 0 := by
  rw [← pow_one (polynomialOriginIdeal n), mem_pow_idealOfVars_iff']
  constructor
  · intro h
    exact h 0 (by simp)
  · intro h d hd
    have hz : d.degree = 0 := by omega
    have hd0 := (Finsupp.degree_eq_zero_iff d).mp hz
    simpa [hd0] using h

/-- The semantic condition in the presentation is precisely membership in the square ideal. -/
theorem noConstantOrLinear_iff_mem_square {n : ℕ} (f : MvPolynomial (Fin n) ℂ) :
    HasNoConstantOrLinear f ↔ f ∈ polynomialOriginIdeal n ^ 2 := by
  rw [mem_pow_idealOfVars_iff']
  constructor
  · rintro ⟨h0, h1⟩ d hd
    by_cases hz : d.degree = 0
    · simpa [(Finsupp.degree_eq_zero_iff d).mp hz] using h0
    · have hdeg : d.degree = 1 := by omega
      have hrange : d ∈ Set.range (fun i : Fin n => Finsupp.single i 1) := by
        rw [Finsupp.range_single_one]
        exact hdeg
      obtain ⟨i, rfl⟩ := hrange
      exact h1 i
  · intro h
    exact ⟨h 0 (by simp), fun i => h (Finsupp.single i 1) (by simp)⟩

def originLinearPart (n : ℕ) : polynomialOriginIdeal n →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi (fun i => (lcoeff ℂ (Finsupp.single i 1)).comp
    ((polynomialOriginIdeal n).subtype.restrictScalars ℂ))

@[simp] theorem originLinearPart_apply (n : ℕ) (f : polynomialOriginIdeal n) (i : Fin n) :
    originLinearPart n f i = (f : MvPolynomial (Fin n) ℂ).coeff (Finsupp.single i 1) := rfl

theorem originLinearPart_mul (n : ℕ) (f g : polynomialOriginIdeal n) :
    originLinearPart n (f * g) = 0 := by
  funext i
  exact (noConstantOrLinear_iff_mem_square _).mpr
    (by simpa [pow_two] using Ideal.mul_mem_mul f.property g.property) |>.2 i

def originCotangentLinear (n : ℕ) : (polynomialOriginIdeal n).Cotangent →ₗ[ℂ] (Fin n → ℂ) :=
  Ideal.Cotangent.lift (originLinearPart n) (originLinearPart_mul n)

@[simp] theorem originCotangentLinear_mk (n : ℕ) (f : polynomialOriginIdeal n) :
    originCotangentLinear n ((polynomialOriginIdeal n).toCotangent f) = originLinearPart n f := rfl

theorem originCotangentLinear_injective (n : ℕ) : Function.Injective (originCotangentLinear n) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro z hz
  obtain ⟨f, rfl⟩ := (polynomialOriginIdeal n).toCotangent_surjective z
  change (polynomialOriginIdeal n).toCotangent f = 0
  apply (Ideal.toCotangent_eq_zero _ _).mpr
  apply (noConstantOrLinear_iff_mem_square _).mp
  refine ⟨(mem_polynomialOriginIdeal_iff _).mp f.property, ?_⟩
  intro i
  exact congrFun hz i

theorem originCotangentLinear_surjective (n : ℕ) : Function.Surjective (originCotangentLinear n) := by
  classical
  intro v
  let f : polynomialOriginIdeal n := ⟨∑ i, v i • X i, by
    rw [mem_polynomialOriginIdeal_iff]
    simp⟩
  refine ⟨(polynomialOriginIdeal n).toCotangent f, ?_⟩
  ext i
  simp [f, originCotangentLinear_mk, originLinearPart_apply, coeff_X, Finsupp.single_left_inj]

/-- The actual cotangent space of the polynomial origin has its usual coordinate basis. -/
def polynomialOriginCotangentEquiv (n : ℕ) :
    (polynomialOriginIdeal n).Cotangent ≃ₗ[ℂ] (Fin n → ℂ) :=
  LinearEquiv.ofBijective (originCotangentLinear n)
    ⟨originCotangentLinear_injective n, originCotangentLinear_surjective n⟩

theorem polynomialOriginCotangent_finrank (n : ℕ) :
    Module.finrank ℂ (polynomialOriginIdeal n).Cotangent = n := by
  rw [(polynomialOriginCotangentEquiv n).finrank_eq]
  simp

end CanonicalRoots
