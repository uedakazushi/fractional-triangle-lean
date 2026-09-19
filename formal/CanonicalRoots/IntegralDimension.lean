import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.KrullDimension.Basic

noncomputable section
namespace CanonicalRoots

section Integral
variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Algebra.IsIntegral A B]

/-- Incomparability makes contraction strictly monotone on chains of primes. -/
theorem integral_prime_comap_strictMono :
    StrictMono (PrimeSpectrum.comap (algebraMap A B)) := by
  intro P Q hPQ
  let : P.asIdeal.IsPrime := P.isPrime
  exact Ideal.IsIntegral.under_lt_under hPQ

theorem integral_ringKrullDim_le : ringKrullDim B ≤ ringKrullDim A :=
  Order.krullDim_le_of_strictMono _ (integral_prime_comap_strictMono A B)

/-- Lying over and going up lift every finite prime chain; no domain hypothesis is needed. -/
theorem integral_ringKrullDim_eq [FaithfulSMul A B] :
    ringKrullDim B = ringKrullDim A := by
  apply le_antisymm (integral_ringKrullDim_le A B)
  change Order.krullDim (PrimeSpectrum A) ≤ Order.krullDim (PrimeSpectrum B)
  unfold Order.krullDim
  apply iSup_le
  intro l
  let : l.head.asIdeal.IsPrime := l.head.isPrime
  obtain ⟨P, hP, hOver⟩ := (inferInstance : Nonempty (l.head.asIdeal.primesOver B))
  let : P.IsPrime := hP
  let : P.LiesOver l.head.asIdeal := hOver
  obtain ⟨L, hlen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  exact le_iSup_of_le L (by rw [hlen])

end Integral
end CanonicalRoots
