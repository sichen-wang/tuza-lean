import Mathlib.Tactic

/-! The arithmetic combining the colored and full-graph covers. -/

namespace Tuza

/-- Arithmetic in the first colored-cover comparison, with denominators cleared. -/
theorem colored_bound_arithmetic {t p a r u : ℕ}
    (hfirst : t + 2 * a + u ≤ 3 * p + r)
    (hsecond : t + r ≤ 2 * p + 3 * a) (hra : r ≤ a) :
    3 * t + 2 * u ≤ 8 * p := by
  omega

/-- Arithmetic after applying the first colored estimate to the residual family. -/
theorem colored_refined_arithmetic {t p a r u : ℕ}
    (hfirst : t + 2 * a + u ≤ 3 * p + r)
    (hresidual : 3 * t + 2 * r ≤ 6 * p + 8 * a) :
    4 * t + u ≤ 9 * p + 6 * a := by
  omega

/-- Equations (3)--(6), combined with weights 20, 8, 19, and 12. -/
theorem four_bounds_arithmetic {t n a b c d h : ℕ}
    (hfirst : t + a ≤ 3 * n)
    (hcut : 8 * t + 8 * c ≤ 12 * n + 20 * a + 12 * b + 3 * h)
    (hbooks : t + c + d ≤ 3 * n)
    (hcolored : 4 * t + 4 * b + h ≤ 12 * n + 9 * c + 6 * d) :
    59 * t + d ≤ 165 * n := by
  omega

end Tuza
