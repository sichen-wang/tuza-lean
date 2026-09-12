import Tuza.Basic.Graph
import Tuza.Basic.Coloring

/-! The complete family of triangles with one red edge. -/

namespace Tuza

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The complete family of triangles with exactly one red edge.
The ambient graph has edge set A; membership in R means red. -/
noncomputable def oneRedTriangles (A R : Finset (Sym2 V)) :
    Finset (Finset (Sym2 V)) := by
  classical
  exact (trianglesOn A).filter (fun T => (T ∩ R).card = 1)

@[simp] theorem mem_oneRedTriangles {A R T : Finset (Sym2 V)} :
    T ∈ oneRedTriangles A R ↔ IsTriangle T ∧ T ⊆ A ∧ (T ∩ R).card = 1 := by
  classical
  simp [oneRedTriangles, and_assoc]

theorem oneRedTriangles_colored (A R : Finset (Sym2 V)) :
    ColoredFamily (oneRedTriangles A R) R := by
  intro T hT
  obtain ⟨ht, _, hr⟩ := mem_oneRedTriangles.mp hT
  exact ⟨ht.card_eq_three, hr⟩

/-- Deleting any edge set preserves completeness of the colored family. -/
theorem oneRedTriangles_sdiff (A R C : Finset (Sym2 V)) :
    oneRedTriangles (A \ C) R = residual (oneRedTriangles A R) C := by
  classical
  ext T
  simp only [oneRedTriangles, mem_filter, trianglesOn_sdiff, mem_residual]
  tauto

theorem oneRedTriangles_subset {A R : Finset (Sym2 V)} :
    oneRedTriangles A R ⊆ trianglesOn A := by
  classical
  exact filter_subset _ _

end Tuza
