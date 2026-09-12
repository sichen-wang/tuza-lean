import Tuza.Construction.Setup
import Tuza.Colored.Exchange
import Tuza.Basic.Coloring
import Tuza.Books.Layered
import Tuza.Probability.Books

/-! Opposite edges outside the packing's new edges give private red pages. -/

namespace Tuza
namespace OppositeEdges

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {edges : Finset (Sym2 V)} (c : Construction edges)

/-- The full type-2 family supplies the ambient graph needed for the exchange. -/
theorem pair_unique_in_special {u v x y : V}
    (hparent : triangleEdges u v x ∈ c.typeTwo)
    (hpage : triangleEdges u v y ∈ c.specialFamily)
    (hspine : s(u, v) ∈ c.newEdges)
    (hopposite : s(x, y) ∈ c.remainingEdges \ c.old)
    (houtside : s(x, y) ∉ c.newEdges) :
    ∀ T ∈ c.specialFamily, s(u, v) ∈ T → T = triangleEdges u v y := by
  have hmax : IsMaximumPacking
      (oneRedTriangles c.remainingEdges (c.remainingEdges \ c.old)) c.typeTwo := by
    rw [← typeTwo_eq_oneRed]
    exact c.typeTwo_maximum
  have hres : triangleEdges u v y ∈
      residual (oneRedTriangles c.remainingEdges (c.remainingEdges \ c.old))
        (blueEdges (c.remainingEdges \ c.old) c.typeTwo) := by
    rw [← typeTwo_eq_oneRed]
    exact c.specialFamily_subset_typeTwo_residual hpage
  have hred : s(u, v) ∈ c.remainingEdges \ c.old :=
    mem_sdiff.mpr ⟨c.newEdges_subset_remaining hspine, (mem_sdiff.mp hspine).2⟩
  have hnot : s(x, y) ∉ redEdges (c.remainingEdges \ c.old) c.typeTwo := by
    rwa [← c.newEdges_eq_red_typeTwo]
  have hu := unique_residual_triangle hmax hparent hres hred
    (mem_sdiff.mp hopposite).1 hopposite hnot
  intro T hT he
  apply hu T ?_ he
  rw [← typeTwo_eq_oneRed]
  exact c.specialFamily_subset_typeTwo_residual hT

theorem pair_mem_privateRed {Q : Finset (Finset (Sym2 V))}
    (hQ : IsPacking c.specialFamily Q) {u v x y : V}
    (hparent : triangleEdges u v x ∈ c.typeTwo)
    (hpage : triangleEdges u v y ∈ Q)
    (hspine : s(u, v) ∈ c.newEdges)
    (hopposite : s(x, y) ∈ c.remainingEdges \ c.old)
    (houtside : s(x, y) ∉ c.newEdges) :
    triangleEdges u v y ∈ privateRedPages c.specialFamily c.newEdges Q := by
  refine mem_privateRedPages.mpr ⟨hpage, ?_⟩
  intro T hT heq
  apply pair_unique_in_special c hparent (hQ.1 hpage) hspine hopposite houtside T hT
  have he : s(u, v) ∈ triangleEdges u v y ∩ c.newEdges :=
    mem_inter.mpr ⟨by simp, hspine⟩
  exact (mem_inter.mp (heq.symm ▸ he)).1

theorem special_member_not_typeTwo {Q : Finset (Finset (Sym2 V))}
    (hQ : IsPacking c.specialFamily Q) {q : Finset (Sym2 V)} (hq : q ∈ Q) :
    q ∉ c.typeTwo := by
  exact Layered.residual_member_not_parent (typeTwo_colored c.remainingEdges c.old)
    (hQ.mono_family c.specialFamily_subset_typeTwo_residual) hq

theorem book_child_private {Q : Finset (Finset (Sym2 V))}
    (hQ : IsPacking c.specialFamily Q) (b : Book V) {p q : Finset (Sym2 V)}
    (hp : p ∈ c.typeTwo) (hpb : p ∈ b.pages) (hq : q ∈ Q) (hqb : q ∈ b.pages)
    (hspine : b.spine ∈ c.newEdges) {e : Sym2 V} (hop : b.opposite = some e)
    (he : e ∈ c.remainingEdges \ c.old) (heout : e ∉ c.newEdges) :
    q ∈ privateRedPages c.specialFamily c.newEdges Q := by
  have hne : q ≠ p := by
    intro heq
    exact special_member_not_typeTwo c hQ hq (heq ▸ hp)
  cases b with
  | single u v x hv => simp [Book.opposite] at hop
  | triple u v x y z hv => simp [Book.opposite] at hop
  | double u v x y hv =>
    have heq : s(x, y) = e := Option.some.inj hop
    subst e
    change s(u, v) ∈ c.newEdges at hspine
    simp only [Book.pages, mem_insert, mem_singleton] at hpb hqb
    rcases hpb with rfl | rfl
    · rcases hqb with hsame | rfl
      · exact (hne hsame).elim
      · exact pair_mem_privateRed c hQ hp hq hspine he heout
    · rcases hqb with rfl | hsame
      · exact pair_mem_privateRed c hQ hp hq hspine
          (Sym2.eq_swap ▸ he) (Sym2.eq_swap ▸ heout)
      · exact (hne hsame).elim

/-- Disjoint book supports give distinct private pages. -/
theorem count_books_le_privateRed {I : Type*} [Fintype I] [DecidableEq I]
    {Q : Finset (Finset (Sym2 V))} (hQ : IsPacking c.specialFamily Q)
    (books : I → Book V) (B : Finset I)
    (hparent : ∀ i, ∃ p ∈ c.typeTwo, p ∈ (books i).pages)
    (hspine : ∀ i, (books i).spine ∈ c.newEdges)
    (hbad : ∀ i ∈ B, ∃ e, (books i).opposite = some e ∧
      e ∈ c.remainingEdges \ c.old ∧ e ∉ c.newEdges)
    (hchild : ∀ i ∈ B, ∃ q ∈ Q, q ∈ (books i).pages)
    (hdis : Books.DisjointSupports (fun i => (books i).pages)) :
    B.card ≤ (privateRedPages c.specialFamily c.newEdges Q).card := by
  classical
  have hs : ∀ i : {j // j ∈ B}, ∃ q,
      q ∈ privateRedPages c.specialFamily c.newEdges Q ∧ q ∈ (books i.val).pages := by
    intro i
    obtain ⟨p, hp, hpb⟩ := hparent i.val
    obtain ⟨q, hq, hqb⟩ := hchild i.val i.property
    obtain ⟨e, hop, he, heout⟩ := hbad i.val i.property
    exact ⟨q, book_child_private c hQ (books i.val) hp hpb hq hqb
      (hspine i.val) hop he heout, hqb⟩
  choose f hfprivate hfpage using hs
  have hinj : Function.Injective f := by
    intro i j heq
    by_contra hne
    have hij : i.val ≠ j.val := fun h => hne (Subtype.ext h)
    have hfiQ := (mem_privateRedPages.mp (hfprivate i)).1
    obtain ⟨e, he⟩ := c.specialFamily_colored.member_nonempty (hQ.1 hfiQ)
    exact disjoint_left.mp (hdis hij)
      (mem_support.mpr ⟨f i, hfpage i, he⟩)
      (mem_support.mpr ⟨f j, hfpage j, heq ▸ he⟩)
  have hsub : univ.image f ⊆ privateRedPages c.specialFamily c.newEdges Q := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := mem_image.mp hq
    exact hfprivate i
  have hcard := card_le_card hsub
  rw [card_image_of_injective _ hinj] at hcard
  simpa using hcard

theorem random_books_card_le_privateRed {I : Type*} [Fintype I] [DecidableEq I]
    {Q : Finset (Finset (Sym2 V))} (hQ : IsPacking c.specialFamily Q)
    (books : I → Book V)
    (hparent : ∀ i, ∃ p ∈ c.typeTwo, p ∈ (books i).pages)
    (hspine : ∀ i, (books i).spine ∈ c.newEdges)
    (hchild : ∀ i ∈ oppositeBooks c.remainingEdges c.oldRemaining c.newEdges books,
      ∃ q ∈ Q, q ∈ (books i).pages)
    (hdis : Books.DisjointSupports (fun i => (books i).pages)) :
    (oppositeBooks c.remainingEdges c.oldRemaining c.newEdges books).card ≤
      (privateRedPages c.specialFamily c.newEdges Q).card := by
  apply count_books_le_privateRed c hQ books
    (oppositeBooks c.remainingEdges c.oldRemaining c.newEdges books) hparent hspine ?_ hchild hdis
  intro i hi
  obtain ⟨e, hop, he, heout⟩ := mem_oppositeBooks.mp hi
  exact ⟨e, hop, c.remaining_sdiff_oldRemaining ▸ he, heout⟩

end OppositeEdges
end Tuza
