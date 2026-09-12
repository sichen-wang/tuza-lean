import Tuza.Construction.Setup
import Tuza.Colored.Covers

/-! The refined colored cover of the full graph: equation (6). -/

namespace Tuza
namespace Construction

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {edges : Finset (Sym2 V)}

/-- The fourth cover consists of the first packing, the old edges of the
remaining packing, and a minimum cover of the complete special family. -/
theorem exists_fourth_cover (c : Construction edges)
    {Q Q1 : Finset (Finset (Sym2 V))}
    (hQ : IsMaximumPacking c.specialFamily Q)
    (hQ1 : IsMaximumPacking (residual c.specialFamily (blueEdges c.newEdges Q)) Q1) :
    ∃ C, IsCover (trianglesOn edges) C ∧
      4 * C.card + 4 * c.typeTwo.card + (privateRedPages c.specialFamily c.newEdges Q).card
      ≤ 12 * c.initial.card + 9 * Q.card + 6 * Q1.card := by
  classical
  have hcolored :
      4 * transversalNumber c.specialFamily + (privateRedPages c.specialFamily c.newEdges Q).card
      ≤ 9 * Q.card + 6 * Q1.card :=
    colored_refined hQ hQ1 (Subset.refl _)
  obtain ⟨D, hD, hDcard⟩ := exists_minimumCover c.specialFamily
    (fun _ hT => c.specialFamily_colored.member_nonempty hT)
  have hDres :
      IsCover (residual (trianglesOn c.remainingEdges) (support c.rest ∩ c.old)) D := by
    rw [← c.specialFamily_eq_residual]
    exact hD
  have hremaining := cover_union_residual hDres
  have hremainingRes : IsCover (residual (trianglesOn edges) (support c.first))
      ((support c.rest ∩ c.old) ∪ D) := by
    rw [← trianglesOn_sdiff edges (support c.first)]
    exact hremaining
  let C := support c.first ∪ ((support c.rest ∩ c.old) ∪ D)
  have hC : IsCover (trianglesOn edges) C := cover_union_residual hremainingRes
  have hCcard : C.card ≤ (support c.first).card + (support c.rest ∩ c.old).card + D.card := by
    calc
      C.card ≤ (support c.first).card + ((support c.rest ∩ c.old) ∪ D).card :=
        card_union_le _ _
      _ ≤ (support c.first).card + ((support c.rest ∩ c.old).card + D.card) :=
        Nat.add_le_add_left (card_union_le _ _) _
      _ = (support c.first).card + (support c.rest ∩ c.old).card + D.card := by omega
  have hfirst : (support c.first).card = 3 * c.first.card :=
    c.first_packing.card_support_uniform (fun _ hT => trianglesOn_card (c.first_packing.1 hT))
  have hrest : (support c.rest).card = 3 * c.rest.card :=
    c.rest_packing.card_support_uniform (fun _ hT => trianglesOn_card (c.rest_packing.1 hT))
  have hnew : (support c.rest \ c.old).card = c.typeTwo.card := c.card_newEdges
  have hsplit := card_sdiff_add_card_inter (support c.rest) c.old
  have hpack := c.first_rest_card_le
  refine ⟨C, hC, ?_⟩
  omega

theorem fourth_cover (c : Construction edges)
    {Q Q1 : Finset (Finset (Sym2 V))}
    (hQ : IsMaximumPacking c.specialFamily Q)
    (hQ1 : IsMaximumPacking (residual c.specialFamily (blueEdges c.newEdges Q)) Q1) :
    4 * transversalNumber (trianglesOn edges) + 4 * c.typeTwo.card +
      (privateRedPages c.specialFamily c.newEdges Q).card
      ≤ 12 * c.initial.card + 9 * Q.card + 6 * Q1.card := by
  obtain ⟨C, hC, hcard⟩ := c.exists_fourth_cover hQ hQ1
  have hbound := hC.number_le
  omega

end Construction
end Tuza
