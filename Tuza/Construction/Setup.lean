import Tuza.Construction.Types

/-! Haxell's packing construction and the complete residual colored family. -/

namespace Tuza

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The three packing choices made before constructing the residual family.
`initial`, `first`, and `rest` are the paper's P, A, and P', respectively. -/
structure Construction (edges : Finset (Sym2 V)) where
  initial : Finset (Finset (Sym2 V))
  initial_maximum : IsMaximumPacking (trianglesOn edges) initial
  first : Finset (Finset (Sym2 V))
  first_maximum : IsMaximumPacking (typeFamily edges (support initial) 1) first
  rest : Finset (Finset (Sym2 V))
  rest_lexMaximum : IsLexMaximumPacking (trianglesOn (edges \ support first))
    (typeFamily (edges \ support first) (support initial) 2) rest

theorem exists_construction (edges : Finset (Sym2 V)) : Nonempty (Construction edges) := by
  obtain ⟨P, hP⟩ := exists_maximumPacking (trianglesOn edges)
  obtain ⟨A, hA⟩ := exists_maximumPacking (typeFamily edges (support P) 1)
  obtain ⟨P', hP'⟩ := exists_lexMaximumPacking (trianglesOn (edges \ support A))
    (typeFamily (edges \ support A) (support P) 2)
  exact ⟨⟨P, hP, A, hA, P', hP'⟩⟩

namespace Construction

variable {edges : Finset (Sym2 V)} (c : Construction edges)

def old : Finset (Sym2 V) := support c.initial
def remainingEdges : Finset (Sym2 V) := edges \ support c.first
def oldRemaining : Finset (Sym2 V) := c.old \ support c.first
noncomputable def typeTwo : Finset (Finset (Sym2 V)) :=
  c.rest ∩ typeFamily c.remainingEdges c.old 2
def newEdges : Finset (Sym2 V) := support c.rest \ c.old

theorem first_packing : IsPacking (trianglesOn edges) c.first :=
  c.first_maximum.1.mono_family (typeFamily_subset _ _ _)

theorem rest_packing : IsPacking (trianglesOn c.remainingEdges) c.rest :=
  c.rest_lexMaximum.1

theorem old_subset_edges : c.old ⊆ edges := by
  intro e he
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  exact (mem_trianglesOn.mp (c.initial_maximum.1.1 hT)).2 heT

theorem rest_support_subset : support c.rest ⊆ c.remainingEdges := by
  intro e he
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  exact (mem_trianglesOn.mp (c.rest_packing.1 hT)).2 heT

theorem oldRemaining_subset_remaining : c.oldRemaining ⊆ c.remainingEdges := by
  intro e he
  exact mem_sdiff.mpr ⟨c.old_subset_edges (mem_sdiff.mp he).1, (mem_sdiff.mp he).2⟩

theorem remaining_old_ge_two {T : Finset (Sym2 V)} (hT : T ∈ trianglesOn c.remainingEdges) :
    2 ≤ (T ∩ c.old).card :=
  old_card_ge_two_after_typeOne c.initial_maximum c.first_maximum hT

theorem remaining_new_le_one {T : Finset (Sym2 V)} (hT : T ∈ trianglesOn c.remainingEdges) :
    (T \ c.old).card ≤ 1 := by
  have hold := c.remaining_old_ge_two hT
  have hcard := trianglesOn_card hT
  have hp := card_sdiff_add_card_inter T c.old
  omega

theorem typeTwo_maximum :
    IsMaximumPacking (typeFamily c.remainingEdges c.old 2) c.typeTwo :=
  c.rest_lexMaximum.typePart_maximum (typeFamily_subset _ _ _)

theorem typeTwo_subset_rest : c.typeTwo ⊆ c.rest := inter_subset_left

theorem newEdges_subset_remaining : c.newEdges ⊆ c.remainingEdges :=
  sdiff_subset.trans c.rest_support_subset

theorem newEdges_disjoint_old : Disjoint c.newEdges c.old := sdiff_disjoint

theorem newEdges_eq_red_typeTwo :
    c.newEdges = redEdges (c.remainingEdges \ c.old) c.typeTwo := by
  ext e
  constructor
  · intro he
    obtain ⟨heP, heO⟩ := mem_sdiff.mp he
    obtain ⟨T, hT, heT⟩ := mem_support.mp heP
    have hactual := c.rest_packing.1 hT
    have htype := new_edge_forces_typeTwo hactual (c.remaining_old_ge_two hactual)
      (mem_sdiff.mpr ⟨heT, heO⟩)
    exact mem_redEdges.mpr ⟨mem_support.mpr ⟨T, mem_inter.mpr ⟨hT, htype⟩, heT⟩,
      mem_sdiff.mpr ⟨c.newEdges_subset_remaining he, heO⟩⟩
  · intro he
    obtain ⟨heB, heR⟩ := mem_redEdges.mp he
    exact mem_sdiff.mpr ⟨support_mono c.typeTwo_subset_rest heB, (mem_sdiff.mp heR).2⟩

theorem card_newEdges : c.newEdges.card = c.typeTwo.card := by
  rw [c.newEdges_eq_red_typeTwo]
  exact c.typeTwo_maximum.1.card_redEdges (typeTwo_colored _ _)

theorem first_rest_card_le : c.first.card + c.rest.card ≤ c.initial.card := by
  have h := deleted_packing_card_add_le c.first_packing c.rest_packing
  rwa [← c.initial_maximum.card_eq] at h

theorem oldRemaining_card : c.oldRemaining.card + c.first.card = 3 * c.initial.card :=
  remaining_old_card c.initial_maximum.1 c.first_maximum.1

theorem rest_covers : IsCover (trianglesOn c.remainingEdges) (support c.rest) :=
  c.rest_lexMaximum.support_covers (fun _ hT => trianglesOn_nonempty hT)

/-- The paper's complete residual family S. -/
noncomputable def specialFamily : Finset (Finset (Sym2 V)) :=
  oneRedTriangles (c.newEdges ∪ (c.oldRemaining \ support c.rest)) c.newEdges

theorem specialFamily_colored : ColoredFamily c.specialFamily c.newEdges :=
  oneRedTriangles_colored _ _

theorem special_edges_subset :
    c.newEdges ∪ (c.oldRemaining \ support c.rest) ⊆ c.remainingEdges :=
  union_subset c.newEdges_subset_remaining
    (sdiff_subset.trans c.oldRemaining_subset_remaining)

theorem specialFamily_subset_triangles : c.specialFamily ⊆ trianglesOn c.remainingEdges := by
  intro T hT
  obtain ⟨ht, hsub, _⟩ := mem_oneRedTriangles.mp hT
  exact mem_trianglesOn.mpr ⟨ht, hsub.trans c.special_edges_subset⟩

/-- Selecting the old edges of P' leaves precisely S. -/
theorem specialFamily_eq_residual :
    c.specialFamily = residual (trianglesOn c.remainingEdges) (support c.rest ∩ c.old) := by
  ext T
  constructor
  · intro hT
    refine mem_residual.mpr ⟨c.specialFamily_subset_triangles hT, disjoint_left.mpr ?_⟩
    intro e heT heSelected
    obtain ⟨heRest, heOld⟩ := mem_inter.mp heSelected
    have he := (mem_oneRedTriangles.mp hT).2.1 heT
    rcases mem_union.mp he with heNew | heBlue
    · exact (mem_sdiff.mp heNew).2 heOld
    · exact (mem_sdiff.mp heBlue).2 heRest
  · intro hT
    obtain ⟨hactual, hd⟩ := mem_residual.mp hT
    obtain ⟨e, he⟩ := c.rest_covers T hactual
    obtain ⟨heT, heRest⟩ := mem_inter.mp he
    have heNotOld : e ∉ c.old := by
      intro heOld
      exact disjoint_left.mp hd heT (mem_inter.mpr ⟨heRest, heOld⟩)
    have heNew : e ∈ c.newEdges := mem_sdiff.mpr ⟨heRest, heNotOld⟩
    have hunique := card_le_one.mp (c.remaining_new_le_one hactual)
    apply mem_oneRedTriangles.mpr
    refine ⟨(mem_trianglesOn.mp hactual).1, ?_, ?_⟩
    · intro f hf
      by_cases hfOld : f ∈ c.old
      · have hfRemain := (mem_trianglesOn.mp hactual).2 hf
        have hfRest : f ∉ support c.rest := by
          intro hfr
          exact disjoint_left.mp hd hf (mem_inter.mpr ⟨hfr, hfOld⟩)
        exact mem_union_right _ (mem_sdiff.mpr
          ⟨mem_sdiff.mpr ⟨hfOld, (mem_sdiff.mp hfRemain).2⟩, hfRest⟩)
      · have hfe := hunique f (mem_sdiff.mpr ⟨hf, hfOld⟩)
          e (mem_sdiff.mpr ⟨heT, heNotOld⟩)
        exact mem_union_left _ (hfe.symm ▸ heNew)
    · apply card_eq_one.mpr
      refine ⟨e, ?_⟩
      ext f
      constructor
      · intro hf
        obtain ⟨hfT, hfNew⟩ := mem_inter.mp hf
        exact mem_singleton.mpr (hunique f
          (mem_sdiff.mpr ⟨hfT, (mem_sdiff.mp hfNew).2⟩)
          e (mem_sdiff.mpr ⟨heT, heNotOld⟩))
      · intro hf
        rw [mem_singleton.mp hf]
        exact mem_inter.mpr ⟨heT, heNew⟩

theorem specialFamily_subset_typeTwo :
    c.specialFamily ⊆ typeFamily c.remainingEdges c.old 2 := by
  intro T hT
  have hactual := c.specialFamily_subset_triangles hT
  have hred := (mem_oneRedTriangles.mp hT).2.2
  obtain ⟨e, he⟩ := card_pos.mp (show 0 < (T ∩ c.newEdges).card by omega)
  obtain ⟨heT, heNew⟩ := mem_inter.mp he
  exact new_edge_forces_typeTwo hactual (c.remaining_old_ge_two hactual)
    (mem_sdiff.mpr ⟨heT, (mem_sdiff.mp heNew).2⟩)

/-- The embedding used to apply the unique-red exchange in the larger graph. -/
theorem specialFamily_subset_typeTwo_residual :
    c.specialFamily ⊆ residual (typeFamily c.remainingEdges c.old 2)
      (blueEdges (c.remainingEdges \ c.old) c.typeTwo) := by
  intro T hT
  refine mem_residual.mpr ⟨c.specialFamily_subset_typeTwo hT, ?_⟩
  have hd := (mem_residual.mp (c.specialFamily_eq_residual ▸ hT)).2
  apply hd.mono_right
  intro e he
  obtain ⟨heB, heNotRed⟩ := mem_blueEdges.mp he
  have heRest := support_mono c.typeTwo_subset_rest heB
  refine mem_inter.mpr ⟨heRest, ?_⟩
  by_contra heNotOld
  exact heNotRed (mem_sdiff.mpr ⟨c.rest_support_subset heRest, heNotOld⟩)

theorem inter_oldRemaining {T : Finset (Sym2 V)} (hT : T ⊆ c.remainingEdges) :
    T ∩ c.oldRemaining = T ∩ c.old := by
  ext e
  constructor
  · intro he
    exact mem_inter.mpr ⟨(mem_inter.mp he).1, (mem_sdiff.mp (mem_inter.mp he).2).1⟩
  · intro he
    obtain ⟨heT, heOld⟩ := mem_inter.mp he
    exact mem_inter.mpr ⟨heT, mem_sdiff.mpr ⟨heOld, (mem_sdiff.mp (hT heT)).2⟩⟩

theorem typeFamily_oldRemaining (j : ℕ) :
    typeFamily c.remainingEdges c.oldRemaining j = typeFamily c.remainingEdges c.old j := by
  ext T
  simp only [mem_typeFamily]
  constructor <;> rintro ⟨hT, hc⟩
  · exact ⟨hT, (c.inter_oldRemaining (mem_trianglesOn.mp hT).2) ▸ hc⟩
  · exact ⟨hT, (c.inter_oldRemaining (mem_trianglesOn.mp hT).2).symm ▸ hc⟩

theorem remaining_sdiff_oldRemaining :
    c.remainingEdges \ c.oldRemaining = c.remainingEdges \ c.old := by
  ext e
  simp only [remainingEdges, oldRemaining, mem_sdiff]
  tauto

theorem remaining_oldRemaining_ge_two {T : Finset (Sym2 V)}
    (hT : T ∈ trianglesOn c.remainingEdges) : 2 ≤ (T ∩ c.oldRemaining).card := by
  rw [c.inter_oldRemaining (mem_trianglesOn.mp hT).2]
  exact c.remaining_old_ge_two hT

theorem old_not_diag {e : Sym2 V} (he : e ∈ c.old) : ¬ e.IsDiag := by
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  intro hd
  have hloop : s(e.diagElem hd, e.diagElem hd) ∈ T :=
    (congrArg (fun f : Sym2 V => f ∈ T) (Sym2.diag_diagElem hd)).mpr heT
  exact (mem_trianglesOn.mp (c.initial_maximum.1.1 hT)).1.not_mem_diag _ hloop

theorem newEdges_not_diag {e : Sym2 V} (he : e ∈ c.newEdges) : ¬ e.IsDiag := by
  obtain ⟨T, hT, heT⟩ := mem_support.mp (mem_sdiff.mp he).1
  intro hd
  have hloop : s(e.diagElem hd, e.diagElem hd) ∈ T :=
    (congrArg (fun f : Sym2 V => f ∈ T) (Sym2.diag_diagElem hd)).mpr heT
  exact (mem_trianglesOn.mp (c.rest_packing.1 hT)).1.not_mem_diag _ hloop

variable {c}

theorem rest_red_eq_sdiff (p : {T // T ∈ c.rest}) :
    p.val ∩ c.newEdges = p.val \ c.old := by
  ext e
  constructor
  · intro he
    exact mem_sdiff.mpr ⟨(mem_inter.mp he).1, (mem_sdiff.mp (mem_inter.mp he).2).2⟩
  · intro he
    obtain ⟨hep, heO⟩ := mem_sdiff.mp he
    exact mem_inter.mpr ⟨hep, mem_sdiff.mpr ⟨mem_support.mpr ⟨p.val, p.property, hep⟩, heO⟩⟩

theorem typeTwo_red_card (p : {T // T ∈ c.typeTwo}) :
    (p.val ∩ c.newEdges).card = 1 := by
  rw [rest_red_eq_sdiff (c := c) ⟨p.val, c.typeTwo_subset_rest p.property⟩]
  change (p.val \ c.old).card = 1
  have ho := (mem_typeFamily.mp (mem_inter.mp p.property).2).2
  have ht := trianglesOn_card (c.rest_packing.1 (c.typeTwo_subset_rest p.property))
  have hs := card_sdiff_add_card_inter p.val c.old
  omega

theorem typeTwo_red_nonempty (p : {T // T ∈ c.typeTwo}) :
    (p.val ∩ c.newEdges).Nonempty := card_pos.mp (by rw [typeTwo_red_card p]; decide)

noncomputable def typeTwoSpine (p : {T // T ∈ c.typeTwo}) : Sym2 V :=
  Classical.choose (typeTwo_red_nonempty p)

theorem typeTwoSpine_mem (p : {T // T ∈ c.typeTwo}) :
    typeTwoSpine p ∈ p.val ∩ c.newEdges :=
  Classical.choose_spec (typeTwo_red_nonempty p)

end Construction

end Tuza
