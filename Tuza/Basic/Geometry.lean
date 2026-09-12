import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic.Tauto

/-! Triangle edges and the geometry of two and three pages. -/

namespace Tuza

variable {V : Type*} [DecidableEq V]

/-- The three unoriented edges on the listed vertices. -/
def triangleEdges (u v w : V) : Finset (Sym2 V) :=
  {s(u, v), s(u, w), s(v, w)}

@[simp]
theorem mem_triangleEdges {e : Sym2 V} {u v w : V} :
    e ∈ triangleEdges u v w ↔ e = s(u, v) ∨ e = s(u, w) ∨ e = s(v, w) := by
  simp [triangleEdges]

/-- A triangle is an edge set on three distinct vertices. -/
def IsTriangle (T : Finset (Sym2 V)) : Prop :=
  ∃ u v w, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ T = triangleEdges u v w

theorem isTriangle_triangleEdges {u v w : V}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    IsTriangle (triangleEdges u v w) :=
  ⟨u, v, w, huv, huw, hvw, rfl⟩

theorem triangleEdges_card {u v w : V}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    (triangleEdges u v w).card = 3 := by
  have h₁ : s(u, v) ≠ s(u, w) := by
    intro h
    exact hvw (Sym2.congr_right.mp h)
  have h₂ : s(u, v) ≠ s(v, w) := by
    intro h
    rcases Sym2.eq_iff.mp h with h | h
    · exact huv h.1
    · exact huw h.1
  have h₃ : s(u, w) ≠ s(v, w) := by
    intro h
    exact huv (Sym2.congr_left.mp h)
  simp [triangleEdges, h₁, h₂, h₃]

theorem IsTriangle.card_eq_three {T : Finset (Sym2 V)} (hT : IsTriangle T) :
    T.card = 3 := by
  rcases hT with ⟨u, v, w, huv, huw, hvw, rfl⟩
  exact triangleEdges_card huv huw hvw

theorem IsTriangle.not_mem_diag {T : Finset (Sym2 V)}
    (hT : IsTriangle T) (z : V) : s(z, z) ∉ T := by
  rcases hT with ⟨u, v, w, huv, huw, hvw, rfl⟩
  simp only [mem_triangleEdges, Sym2.eq_iff]
  aesop

theorem IsTriangle.ne_of_mem {T : Finset (Sym2 V)} (hT : IsTriangle T)
    {u v : V} (h : s(u, v) ∈ T) : u ≠ v := by
  rintro rfl
  exact hT.not_mem_diag u h

/-- Any two edges of a triangle have a common endpoint. -/
theorem IsTriangle.edges_incident {T : Finset (Sym2 V)} (hT : IsTriangle T)
    {e f : Sym2 V} (he : e ∈ T) (hf : f ∈ T) :
    ∃ z : V, z ∈ e ∧ z ∈ f := by
  rcases hT with ⟨u, v, w, huv, huw, hvw, rfl⟩
  rcases mem_triangleEdges.mp he with rfl | rfl | rfl <;>
    rcases mem_triangleEdges.mp hf with rfl | rfl | rfl
  · exact ⟨u, by simp, by simp⟩
  · exact ⟨u, by simp, by simp⟩
  · exact ⟨v, by simp, by simp⟩
  · exact ⟨u, by simp, by simp⟩
  · exact ⟨u, by simp, by simp⟩
  · exact ⟨w, by simp, by simp⟩
  · exact ⟨v, by simp, by simp⟩
  · exact ⟨w, by simp, by simp⟩
  · exact ⟨v, by simp, by simp⟩

/-- Two distinct edges incident at a vertex determine the triangle. -/
theorem IsTriangle.eq_of_spokes {T : Finset (Sym2 V)} (hT : IsTriangle T)
    {u v w : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (he : s(u, v) ∈ T) (hf : s(u, w) ∈ T) :
    T = triangleEdges u v w := by
  rcases hT with ⟨a, b, c, hab, hac, hbc, rfl⟩
  simp only [mem_triangleEdges, Sym2.eq_iff] at he hf
  rcases he with h | h | h <;>
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    rcases hf with h | h | h <;>
    rcases h with ⟨hc, hd⟩ | ⟨hc, hd⟩ <;>
    subst_vars <;>
    simp_all [triangleEdges, Sym2.eq_swap, Finset.insert_comm]
  all_goals
    ext e
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

theorem IsTriangle.exists_third_of_mem {T : Finset (Sym2 V)}
    (hT : IsTriangle T) {u v : V} (he : s(u, v) ∈ T) :
    ∃ w, u ≠ w ∧ v ≠ w ∧ T = triangleEdges u v w := by
  rcases hT with ⟨a, b, c, hab, hac, hbc, rfl⟩
  simp only [mem_triangleEdges, Sym2.eq_iff] at he
  rcases he with h | h | h
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨c, hac, hbc, rfl⟩
    · refine ⟨c, hbc, hac, ?_⟩
      ext e
      simp [triangleEdges, Sym2.eq_swap, or_comm]
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨b, hab, hbc.symm, ?_⟩
      ext e
      simp [triangleEdges, Sym2.eq_swap, or_left_comm]
    · refine ⟨b, hbc.symm, hab, ?_⟩
      ext e
      simp [triangleEdges, Sym2.eq_swap, or_comm, or_assoc]
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨a, hab.symm, hac.symm, ?_⟩
      ext e
      simp [triangleEdges, Sym2.eq_swap, or_comm, or_left_comm]
    · refine ⟨a, hac.symm, hab.symm, ?_⟩
      ext e
      simp [triangleEdges, Sym2.eq_swap, or_comm, or_assoc]

theorem IsTriangle.eq_of_two_common_edges {T U : Finset (Sym2 V)}
    (hT : IsTriangle T) (hU : IsTriangle U) {e f : Sym2 V}
    (hef : e ≠ f) (heT : e ∈ T) (hfT : f ∈ T)
    (heU : e ∈ U) (hfU : f ∈ U) : T = U := by
  obtain ⟨u, hue, huf⟩ := hT.edges_incident heT hfT
  obtain ⟨v, rfl⟩ := Sym2.mem_iff_exists.mp hue
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp huf
  have huv : u ≠ v := hT.ne_of_mem heT
  have huw : u ≠ w := hT.ne_of_mem hfT
  have hvw : v ≠ w := by
    rintro rfl
    exact hef rfl
  exact (hT.eq_of_spokes huv huw hvw heT hfT).trans
    (hU.eq_of_spokes huv huw hvw heU hfU).symm

theorem IsTriangle.inter_card_le_one {T U : Finset (Sym2 V)}
    (hT : IsTriangle T) (hU : IsTriangle U) (hne : T ≠ U) :
    (T ∩ U).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  by_contra hef
  exact hne (hT.eq_of_two_common_edges hU hef
    (Finset.mem_inter.mp he).1 (Finset.mem_inter.mp hf).1
    (Finset.mem_inter.mp he).2 (Finset.mem_inter.mp hf).2)

/-- Triangles whose listed vertices have only the first vertex in common share no edge. -/
theorem triangleEdges_disjoint_of_five_distinct {u v w x y : V}
    (hvertices : [u, v, w, x, y].Nodup) :
    Disjoint (triangleEdges u v w) (triangleEdges u x y) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  rcases mem_triangleEdges.mp he with rfl | rfl | rfl <;>
    simp_all [mem_triangleEdges, List.nodup_cons]

/-- A triangle meeting both pages and missing their spine uses the opposite edge. -/
theorem two_page_triangle {T : Finset (Sym2 V)} (hT : IsTriangle T)
    {u v x y : V} (hvertices : [u, v, x, y].Nodup)
    (hspine : s(u, v) ∉ T)
    (hx : (T ∩ triangleEdges u v x).Nonempty)
    (hy : (T ∩ triangleEdges u v y).Nonempty) :
    T = triangleEdges u x y ∨ T = triangleEdges v x y := by
  have hdistinct : u ≠ v ∧ u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y ∧ x ≠ y := by
    simpa [List.nodup_cons, and_assoc] using hvertices
  rcases hdistinct with ⟨huv, hux, huy, hvx, hvy, hxy⟩
  obtain ⟨e, he⟩ := hx
  obtain ⟨heT, heX⟩ := Finset.mem_inter.mp he
  obtain ⟨f, hf⟩ := hy
  obtain ⟨hfT, hfY⟩ := Finset.mem_inter.mp hf
  rcases mem_triangleEdges.mp heX with rfl | rfl | rfl <;>
    rcases mem_triangleEdges.mp hfY with rfl | rfl | rfl
  all_goals try exact (hspine heT).elim
  all_goals try exact (hspine hfT).elim
  · exact Or.inl (hT.eq_of_spokes hux huy hxy heT hfT)
  · obtain ⟨z, hz, hz'⟩ := hT.edges_incident heT hfT
    simp only [Sym2.mem_iff] at hz hz'
    rcases hz with rfl | rfl <;> rcases hz' with h | h <;> simp_all
  · obtain ⟨z, hz, hz'⟩ := hT.edges_incident heT hfT
    simp only [Sym2.mem_iff] at hz hz'
    rcases hz with rfl | rfl <;> rcases hz' with h | h <;> simp_all
  · exact Or.inr (hT.eq_of_spokes hvx hvy hxy heT hfT)

theorem two_page_opposite_mem {T : Finset (Sym2 V)} (hT : IsTriangle T)
    {u v x y : V} (hvertices : [u, v, x, y].Nodup)
    (hspine : s(u, v) ∉ T)
    (hx : (T ∩ triangleEdges u v x).Nonempty)
    (hy : (T ∩ triangleEdges u v y).Nonempty) : s(x, y) ∈ T := by
  rcases two_page_triangle hT hvertices hspine hx hy with rfl | rfl <;> simp

/-- A triangle meeting three distinct pages must contain their common spine. -/
theorem three_page_spine {T : Finset (Sym2 V)} (hT : IsTriangle T)
    {u v x y z : V} (hvertices : [u, v, x, y, z].Nodup)
    (hx : (T ∩ triangleEdges u v x).Nonempty)
    (hy : (T ∩ triangleEdges u v y).Nonempty)
    (hz : (T ∩ triangleEdges u v z).Nonempty) : s(u, v) ∈ T := by
  by_contra hspine
  have hfour : [u, v, x, y].Nodup := by
    simp_all [List.nodup_cons]
  obtain ⟨e, he⟩ := hz
  obtain ⟨heT, heZ⟩ := Finset.mem_inter.mp he
  rcases two_page_triangle hT hfour hspine hx hy with h | h <;>
    rw [h] at heT <;>
    rcases mem_triangleEdges.mp heT with rfl | rfl | rfl <;>
    simp_all [mem_triangleEdges, List.nodup_cons] <;> aesop

end Tuza
