import CanonicalRoots.AdicScalarExtension

noncomputable section
namespace CanonicalRoots

variable {R S T U : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
  [Algebra R S] [Algebra R T] [Algebra R U] (I : Ideal R)

/-- The actual algebra map on each quotient by a power of the extended ideal. -/
def adicAlgebraQuotientMap (f : S →ₐ[R] T) (n : ℕ) :
    (S ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Ideal S)) →ₐ[R]
      (T ⧸ ((I.map (algebraMap R T)) ^ n • ⊤ : Ideal T)) :=
  Ideal.quotientMapₐ _ f (by
    simp only [Ideal.smul_eq_mul, Ideal.mul_top]
    apply Ideal.map_le_iff_le_comap.mp
    rw [Ideal.map_pow]
    change Ideal.map f.toRingHom (I.map (algebraMap R S)) ^ n ≤ _
    rw [Ideal.map_map]
    have hf : f.toRingHom.comp (algebraMap R S) = algebraMap R T := f.comp_algebraMap
    rw [hf])

def adicAlgebraMapLinear (f : S →ₐ[R] T) :
    AdicCompletion (I.map (algebraMap R S)) S →ₗ[R]
      AdicCompletion (I.map (algebraMap R T)) T :=
  (adicScalarExtensionEquiv I).toLinearMap.comp
    (((AdicCompletion.map I f.toLinearMap).restrictScalars R).comp
      (adicScalarExtensionEquiv I).symm.toLinearMap)

theorem adicAlgebraMapLinear_val (f : S →ₐ[R] T)
    (x : AdicCompletion (I.map (algebraMap R S)) S) (n : ℕ) :
    (adicAlgebraMapLinear I f x).val n = adicAlgebraQuotientMap I f n (x.val n) := by
  change adicScalarQuotientEquiv I n
      (f.toLinearMap.reduceModIdeal (I ^ n) ((adicScalarQuotientEquiv I n).symm (x.val n))) = _
  generalize x.val n = y
  induction y using Submodule.Quotient.induction_on with | _ y => rfl

/-- Completion is functorial for algebra maps at ideals extended from the common base. -/
def adicAlgebraMap (f : S →ₐ[R] T) :
    AdicCompletion (I.map (algebraMap R S)) S →ₐ[R]
      AdicCompletion (I.map (algebraMap R T)) T :=
  AlgHom.ofLinearMap (adicAlgebraMapLinear I f) (by
    apply Subtype.ext
    funext n
    rw [adicAlgebraMapLinear_val]
    exact map_one (adicAlgebraQuotientMap I f n)) (fun x y => by
    apply Subtype.ext
    funext n
    rw [adicAlgebraMapLinear_val]
    change adicAlgebraQuotientMap I f n (x.val n * y.val n) =
      (adicAlgebraMapLinear I f x).val n * (adicAlgebraMapLinear I f y).val n
    rw [map_mul, adicAlgebraMapLinear_val, adicAlgebraMapLinear_val])

@[simp] theorem adicAlgebraMap_val (f : S →ₐ[R] T)
    (x : AdicCompletion (I.map (algebraMap R S)) S) (n : ℕ) :
    (adicAlgebraMap I f x).val n = adicAlgebraQuotientMap I f n (x.val n) :=
  adicAlgebraMapLinear_val I f x n

@[simp] theorem adicAlgebraMap_id : adicAlgebraMap I (AlgHom.id R S) = AlgHom.id _ _ := by
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  funext n
  rw [adicAlgebraMap_val]
  change adicAlgebraQuotientMap I (AlgHom.id R S) n (x.val n) = x.val n
  generalize x.val n = y
  induction y using Submodule.Quotient.induction_on with | _ y => rfl

theorem adicAlgebraMap_comp (f : S →ₐ[R] T) (g : T →ₐ[R] U) :
    adicAlgebraMap I (g.comp f) = (adicAlgebraMap I g).comp (adicAlgebraMap I f) := by
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  funext n
  change (adicAlgebraMap I (g.comp f) x).val n =
    (adicAlgebraMap I g (adicAlgebraMap I f x)).val n
  simp only [adicAlgebraMap_val]
  generalize x.val n = y
  induction y using Submodule.Quotient.induction_on with | _ y => rfl

/-- The quotient-level base inclusion, with no change to the original source ideal. -/
def adicBaseQuotientMap (n : ℕ) :
    (R ⧸ (I ^ n • ⊤ : Ideal R)) →ₐ[R]
      (S ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Ideal S)) :=
  Ideal.quotientMapₐ _ (Algebra.ofId R S) (by
    simp only [Ideal.smul_eq_mul, Ideal.mul_top]
    apply Ideal.map_le_iff_le_comap.mp
    change Ideal.map (algebraMap R S) (I ^ n) ≤ _
    rw [Ideal.map_pow])

def adicBaseMapLinear : AdicCompletion I R →ₗ[R] AdicCompletion (I.map (algebraMap R S)) S :=
  (adicScalarExtensionEquiv I).toLinearMap.comp
    ((AdicCompletion.map I (Algebra.linearMap R S)).restrictScalars R)

theorem adicBaseMapLinear_val (x : AdicCompletion I R) (n : ℕ) :
    (adicBaseMapLinear (S := S) I x).val n = adicBaseQuotientMap I n (x.val n) := by
  change adicScalarQuotientEquiv I n
    ((Algebra.linearMap R S).reduceModIdeal (I ^ n) (x.val n)) = _
  generalize x.val n = y
  induction y using Submodule.Quotient.induction_on with | _ y => rfl

/-- The canonical algebra map from the base completion to the extended-ideal completion. -/
def adicBaseMap : AdicCompletion I R →ₐ[R] AdicCompletion (I.map (algebraMap R S)) S :=
  AlgHom.ofLinearMap (adicBaseMapLinear I) (by
    apply Subtype.ext
    funext n
    rw [adicBaseMapLinear_val]
    exact map_one (adicBaseQuotientMap I n)) (fun x y => by
    apply Subtype.ext
    funext n
    rw [adicBaseMapLinear_val]
    change adicBaseQuotientMap I n (x.val n * y.val n) =
      (adicBaseMapLinear I x).val n * (adicBaseMapLinear I y).val n
    rw [map_mul, adicBaseMapLinear_val, adicBaseMapLinear_val])

theorem adicAlgebraMap_comp_base (f : S →ₐ[R] T) :
    (adicAlgebraMap I f).comp (adicBaseMap I) = adicBaseMap I := by
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  funext n
  change (adicAlgebraMap I f (adicBaseMapLinear I x)).val n = (adicBaseMapLinear I x).val n
  rw [adicAlgebraMap_val, adicBaseMapLinear_val, adicBaseMapLinear_val]
  generalize x.val n = y
  induction y using Submodule.Quotient.induction_on with
  | _ y => exact congrArg (Ideal.Quotient.mk _) (f.commutes y)

end CanonicalRoots
