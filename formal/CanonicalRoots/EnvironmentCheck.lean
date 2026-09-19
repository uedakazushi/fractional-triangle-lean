import Mathlib

/- This is a smoke test only. It is NOT a classification theorem.
   The handoff author has not compiled this file. -/
namespace CanonicalRoots

theorem environment_ring_identity (x y : ℤ) :
    (x + y)^2 = x^2 + 2*x*y + y^2 := by
  ring

end CanonicalRoots
