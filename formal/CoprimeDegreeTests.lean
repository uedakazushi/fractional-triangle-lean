import CanonicalRoots.CoprimeRootScale

noncomputable section
open CanonicalRoots

private theorem admissible23767 : AdmissibleSignature ![2,3,7,67] := by
  constructor
  · decide +kernel
  · norm_num [Fin.sum_univ_succ]

-- The nonmaximal root scale is retained; pairwise coprimality alone does not imply R=T.
example : ∃ τ : DegreeGroup ![2,3,7,67], IsCanonicalRoot ![2,3,7,67] 5 τ ∧
    productDegree ![2,3,7,67] τ = 5 ∧
    ∀ k : ℕ, (∃ m : ℕ, k • xDegree ![2,3,7,67] 0 = m • τ) ↔ 5 ∣ k := by
  obtain ⟨τ, hτ⟩ := (canonicalRoot_exists_iff ![2,3,7,67] (by decide +kernel) (a := 5)).mpr
    (by decide +kernel)
  have hcop : Pairwise (fun i j => Nat.Coprime ((![2,3,7,67] : Fin 4 → ℕ) i) (![2,3,7,67] j)) :=
    by unfold Pairwise; decide +kernel
  refine ⟨τ, hτ, ?_, ?_⟩
  · simpa only [show canonicalRootScale ![2,3,7,67] 5 = 5 from by decide +kernel, Nat.cast_ofNat] using
      productDegree_canonicalRoot ![2,3,7,67] admissible23767 (by decide) τ hτ hcop
  · intro k
    simpa only [show canonicalRootScale ![2,3,7,67] 5 = 5 from by decide +kernel] using
      pure_power_root_degree_iff ![2,3,7,67] admissible23767 (by decide) τ hτ hcop 0 k

-- The integral degree map is an equivalence of the original group, not its rationalization.
example : Nonempty (DegreeGroup ![2,3,7,67] ≃+ ℤ) :=
  ⟨coprimeDegreeEquiv ![2,3,7,67] (by decide +kernel) (by unfold Pairwise; decide +kernel)⟩

end
