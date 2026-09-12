import Tuza.Colored.Family

/-! The two-for-one exchange: Lemma 2.1. -/

namespace Tuza

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
private theorem red_edges_eq {T R : Finset (Sym2 V)}
    (hcard : (T ∩ R).card = 1) {e f : Sym2 V}
    (he : e ∈ T) (heR : e ∈ R) (hf : f ∈ T) (hfR : f ∈ R) : e = f := by
  exact Finset.card_le_one.mp (Nat.le_of_eq hcard)
    e (mem_inter.mpr ⟨he, heR⟩) f (mem_inter.mpr ⟨hf, hfR⟩)

/-- The two-for-one exchange in Lemma 2.1 of the manuscript. -/
theorem unique_residual_triangle {A R : Finset (Sym2 V)}
    {P : Finset (Finset (Sym2 V))} {u v x y : V}
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hparent : triangleEdges u v x ∈ P)
    (hpage : triangleEdges u v y ∈
      residual (oneRedTriangles A R) (blueEdges R P))
    (hspine : s(u, v) ∈ R)
    (hoppA : s(x, y) ∈ A) (hoppR : s(x, y) ∈ R)
    (hoppNew : s(x, y) ∉ redEdges R P) :
    ∀ T ∈ residual (oneRedTriangles A R) (blueEdges R P),
      s(u, v) ∈ T → T = triangleEdges u v y := by
  classical
  obtain ⟨hX, hXA, hXR⟩ := mem_oneRedTriangles.mp (hP.1.1 hparent)
  obtain ⟨hpageF, hpageDisj⟩ := mem_residual.mp hpage
  obtain ⟨hY, hYA, hYR⟩ := mem_oneRedTriangles.mp hpageF
  have huv : u ≠ v := hX.ne_of_mem (by simp)
  have hux : u ≠ x := hX.ne_of_mem (by simp)
  have hvx : v ≠ x := hX.ne_of_mem (by simp)
  have huy : u ≠ y := hY.ne_of_mem (by simp)
  have hvy : v ≠ y := hY.ne_of_mem (by simp)

  have huxNotRed : s(u, x) ∉ R := by
    intro hred
    have heq := red_edges_eq hXR (by simp) hred (by simp) hspine
    exact hvx (Sym2.congr_right.mp heq).symm
  have huyNotRed : s(u, y) ∉ R := by
    intro hred
    have heq := red_edges_eq hYR (by simp) hred (by simp) hspine
    exact hvy (Sym2.congr_right.mp heq).symm
  have huxBlue : s(u, x) ∈ blueEdges R P := by
    exact mem_sdiff.mpr ⟨mem_support.mpr ⟨triangleEdges u v x, hparent, by simp⟩,
      huxNotRed⟩
  have hxy : x ≠ y := by
    intro h
    exact disjoint_left.mp hpageDisj (by simp [h]) huxBlue
  have huyOutside : s(u, y) ∉ support P := by
    intro hs
    exact disjoint_left.mp hpageDisj (by simp)
      (mem_sdiff.mpr ⟨hs, huyNotRed⟩)
  have hxyOutside : s(x, y) ∉ support P := by
    intro hs
    exact hoppNew (mem_inter.mpr ⟨hs, hoppR⟩)

  intro T hT huvT
  have hTreal := (mem_oneRedTriangles.mp (mem_residual.mp hT).1).1
  obtain ⟨z, huz, hvz, rfl⟩ := hTreal.exists_third_of_mem huvT
  by_contra hne
  obtain ⟨hTF, hTDisj⟩ := mem_residual.mp hT
  obtain ⟨hZ, hZA, hZR⟩ := mem_oneRedTriangles.mp hTF
  have hxz : x ≠ z := by
    intro h
    exact disjoint_left.mp hTDisj (by simp [h]) huxBlue
  have hyz : y ≠ z := by
    intro h
    apply hne
    subst z
    rfl

  have hnew : triangleEdges u x y ∈ oneRedTriangles A R := by
    apply mem_oneRedTriangles.mpr
    refine ⟨isTriangle_triangleEdges hux huy hxy, ?_, ?_⟩
    · intro e he
      rcases mem_triangleEdges.mp he with rfl | rfl | rfl
      · exact hXA (by simp)
      · exact hYA (by simp)
      · exact hoppA
    · have hinter : triangleEdges u x y ∩ R = {s(x, y)} := by
        ext e
        simp only [mem_inter, mem_triangleEdges, mem_singleton]
        constructor
        · rintro ⟨he, hr⟩
          rcases he with rfl | rfl | rfl
          · exact (huxNotRed hr).elim
          · exact (huyNotRed hr).elim
          · rfl
        · rintro rfl
          exact ⟨Or.inr (Or.inr rfl), hoppR⟩
      simp [hinter]

  have hvertices : [u, x, y, v, z].Nodup := by
    simp [List.nodup_cons, hux, huy, huv, huz, hxy, hvx.symm, hxz,
      hvy.symm, hyz, hvz]
  have hnewDisj : Disjoint (triangleEdges u x y) (triangleEdges u v z) :=
    triangleEdges_disjoint_of_five_distinct hvertices
  have hnewRest : Disjoint (triangleEdges u x y)
      (support (P.erase (triangleEdges u v x))) := by
    apply hP.1.disjoint_support_erase hparent
    intro e he hs
    rcases mem_triangleEdges.mp he with rfl | rfl | rfl
    · simp
    · exact (huyOutside hs).elim
    · exact (hxyOutside hs).elim
  have hotherRest : Disjoint (triangleEdges u v z)
      (support (P.erase (triangleEdges u v x))) := by
    apply hP.1.disjoint_support_erase hparent
    intro e he hs
    have hr : e ∈ R := by
      by_contra hr
      exact disjoint_left.mp hTDisj he (mem_sdiff.mpr ⟨hs, hr⟩)
    have heq := red_edges_eq hZR he hr (by simp) hspine
    rw [heq]
    simp
  exact hP.no_two_for_one hparent hnew hTF
    ⟨s(u, x), by simp⟩ ⟨s(u, v), by simp⟩ hnewDisj hnewRest hotherRest

end Tuza
