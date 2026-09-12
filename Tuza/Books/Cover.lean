import Tuza.Basic.Geometry
import Tuza.Basic.Packing
import Tuza.Books.Families

/-!
Books with one to three pages and their covers: Lemma 2.2.

A two-page cover includes the opposite vertex pair. Restricting the cover to the
graph's edges preserves coverage and can only reduce its size.
-/

namespace Tuza

open Finset
open scoped BigOperators

variable {V : Type*}

/-- Books with one, two, or three distinct pages and their actual vertices. -/
inductive Book (V : Type*) where
  | single (u v x : V) (vertices : [u, v, x].Nodup)
  | double (u v x y : V) (vertices : [u, v, x, y].Nodup)
  | triple (u v x y z : V) (vertices : [u, v, x, y, z].Nodup)

namespace Book

def spine : Book V → Sym2 V
  | .single u v _ _ => s(u, v)
  | .double u v _ _ _ => s(u, v)
  | .triple u v _ _ _ _ => s(u, v)

/-- Only a two-page book has an opposite edge relevant to its cover. -/
def opposite : Book V → Option (Sym2 V)
  | .single .. => none
  | .double _ _ x y _ => some s(x, y)
  | .triple .. => none

def pageCount : Book V → ℕ
  | .single .. => 1
  | .double .. => 2
  | .triple .. => 3

variable [DecidableEq V]

def pages : Book V → Finset (Finset (Sym2 V))
  | .single u v x _ => {triangleEdges u v x}
  | .double u v x y _ => {triangleEdges u v x, triangleEdges u v y}
  | .triple u v x y z _ =>
      {triangleEdges u v x, triangleEdges u v y, triangleEdges u v z}

def cover : Book V → Finset (Sym2 V)
  | .single u v x _ => triangleEdges u v x
  | .double u v x y _ => {s(u, v), s(x, y)}
  | .triple u v _ _ _ _ => {s(u, v)}

omit [DecidableEq V] in
@[simp] theorem opposite_double (u v x y : V) (h : [u, v, x, y].Nodup) :
    (Book.double u v x y h).opposite = some s(x, y) := rfl

@[simp] theorem cover_double (u v x y : V) (h : [u, v, x, y].Nodup) :
    (Book.double u v x y h).cover = {s(u, v), s(x, y)} := rfl

private theorem pages_ne {u v x y : V} (h : [u, v, x, y].Nodup) :
    triangleEdges u v x ≠ triangleEdges u v y := by
  have hd : u ≠ v ∧ u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y ∧ x ≠ y := by
    simpa [List.nodup_cons, and_assoc] using h
  intro heq
  have hx : s(u, x) ∈ triangleEdges u v y := heq ▸ (by simp)
  simp only [mem_triangleEdges, Sym2.eq_iff] at hx
  aesop

theorem pages_nonempty (b : Book V) : b.pages.Nonempty := by
  cases b <;> simp [pages]

theorem pages_card (b : Book V) : b.pages.card = b.pageCount := by
  cases b with
  | single u v x h => simp [pages, pageCount]
  | double u v x y h => simp [pages, pageCount, pages_ne h]
  | triple u v x y z h =>
    have hxy : [u, v, x, y].Nodup := by simp_all [List.nodup_cons]
    have hxz : [u, v, x, z].Nodup := by simp_all [List.nodup_cons]
    have hyz : [u, v, y, z].Nodup := by simp_all [List.nodup_cons]
    simp [pages, pageCount, pages_ne hxy, pages_ne hxz, pages_ne hyz]

theorem pages_card_le_three (b : Book V) : b.pages.card ≤ 3 := by
  rw [pages_card]
  cases b <;> simp [pageCount]

theorem page_isTriangle (b : Book V) {T : Finset (Sym2 V)} (hT : T ∈ b.pages) :
    IsTriangle T := by
  cases b with
  | single u v x h =>
    simp only [pages, mem_singleton] at hT
    subst T
    apply isTriangle_triangleEdges <;> simp_all [List.nodup_cons]
  | double u v x y h =>
    simp only [pages, mem_insert, mem_singleton] at hT
    rcases hT with rfl | rfl <;>
      apply isTriangle_triangleEdges <;> simp_all [List.nodup_cons]
  | triple u v x y z h =>
    simp only [pages, mem_insert, mem_singleton] at hT
    rcases hT with rfl | rfl | rfl <;>
      apply isTriangle_triangleEdges <;> simp_all [List.nodup_cons]

theorem spine_mem_page (b : Book V) {T : Finset (Sym2 V)} (hT : T ∈ b.pages) :
    b.spine ∈ T := by
  cases b <;> simp_all [pages, spine] <;> aesop

theorem cover_card_add_pages_card_le_four (b : Book V) :
    b.cover.card + b.pages.card ≤ 4 := by
  rw [pages_card]
  cases b with
  | single u v x h =>
    have huv : u ≠ v := by simp_all [List.nodup_cons]
    have hux : u ≠ x := by simp_all [List.nodup_cons]
    have hvx : v ≠ x := by simp_all [List.nodup_cons]
    simp [cover, pageCount, triangleEdges_card huv hux hvx]
  | double u v x y h =>
    have hc : ({s(u, v), s(x, y)} : Finset (Sym2 V)).card ≤ 2 := card_le_two
    simp only [cover, pageCount]
    omega
  | triple u v x y z h => simp [cover, pageCount]

/-- Meeting every page of an actual book forces a triangle to meet its cover. -/
theorem meets_cover (b : Book V) {T : Finset (Sym2 V)} (hT : IsTriangle T)
    (hmeet : ∀ U ∈ b.pages, (T ∩ U).Nonempty) : (T ∩ b.cover).Nonempty := by
  cases b with
  | single u v x h => exact hmeet (triangleEdges u v x) (by simp [pages])
  | double u v x y h =>
    by_cases he : s(u, v) ∈ T
    · exact ⟨s(u, v), mem_inter.mpr ⟨he, by simp [cover]⟩⟩
    · have hop := two_page_opposite_mem hT h he
        (hmeet (triangleEdges u v x) (by simp [pages]))
        (hmeet (triangleEdges u v y) (by simp [pages]))
      exact ⟨s(x, y), mem_inter.mpr ⟨hop, by simp [cover]⟩⟩
  | triple u v x y z h =>
    have he := three_page_spine hT h
      (hmeet (triangleEdges u v x) (by simp [pages]))
      (hmeet (triangleEdges u v y) (by simp [pages]))
      (hmeet (triangleEdges u v z) (by simp [pages]))
    exact ⟨s(u, v), mem_inter.mpr ⟨he, by simp [cover]⟩⟩

theorem meets_cover_of_not_disjoint (b : Book V) {T : Finset (Sym2 V)}
    (hT : IsTriangle T) (hmeet : ∀ U ∈ b.pages, ¬ Disjoint T U) :
    (T ∩ b.cover).Nonempty := by
  apply b.meets_cover hT
  intro U hU
  obtain ⟨e, heT, heU⟩ := not_disjoint_iff.mp (hmeet U hU)
  exact ⟨e, mem_inter.mpr ⟨heT, heU⟩⟩

/-- Every nonempty family of at most three actual triangles with a common edge
has one of the three book representations above, with that precise spine. -/
theorem exists_representation (S : Finset (Finset (Sym2 V))) (e : Sym2 V)
    (hne : S.Nonempty) (hcard : S.card ≤ 3)
    (htri : ∀ T ∈ S, IsTriangle T) (hspine : ∀ T ∈ S, e ∈ T) :
    ∃ b : Book V, b.pages = S ∧ b.spine = e := by
  obtain ⟨u, v, rfl⟩ : ∃ u v, e = s(u, v) :=
    Sym2.inductionOn e (fun u v => ⟨u, v, rfl⟩)
  have huv : u ≠ v := by
    obtain ⟨T, hT⟩ := hne
    exact (htri T hT).ne_of_mem (hspine T hT)
  have hr (T : Finset (Sym2 V)) (hT : T ∈ S) :
      ∃ x, u ≠ x ∧ v ≠ x ∧ T = triangleEdges u v x :=
    (htri T hT).exists_third_of_mem (hspine T hT)
  have hcpos : 0 < S.card := card_pos.mpr hne
  have hc : S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by omega
  rcases hc with hc | hc | hc
  · obtain ⟨T, rfl⟩ := card_eq_one.mp hc
    obtain ⟨x, hux, hvx, rfl⟩ := hr T (by simp)
    have hv : [u, v, x].Nodup := by simp [List.nodup_cons, huv, hux, hvx]
    exact ⟨.single u v x hv, rfl, rfl⟩
  · obtain ⟨T, U, hTU, rfl⟩ := card_eq_two.mp hc
    obtain ⟨x, hux, hvx, rfl⟩ := hr T (by simp)
    obtain ⟨y, huy, hvy, rfl⟩ := hr U (by simp)
    have hxy : x ≠ y := by rintro rfl; exact hTU rfl
    have hv : [u, v, x, y].Nodup := by
      simp [List.nodup_cons, huv, hux, huy, hvx, hvy, hxy]
    exact ⟨.double u v x y hv, rfl, rfl⟩
  · obtain ⟨T, U, W, hTU, hTW, hUW, rfl⟩ := card_eq_three.mp hc
    obtain ⟨x, hux, hvx, rfl⟩ := hr T (by simp)
    obtain ⟨y, huy, hvy, rfl⟩ := hr U (by simp)
    obtain ⟨z, huz, hvz, rfl⟩ := hr W (by simp)
    have hxy : x ≠ y := by rintro rfl; exact hTU rfl
    have hxz : x ≠ z := by rintro rfl; exact hTW rfl
    have hyz : y ≠ z := by rintro rfl; exact hUW rfl
    have hv : [u, v, x, y, z].Nodup := by
      simp [List.nodup_cons, huv, hux, huy, huz, hvx, hvy, hvz, hxy, hxz, hyz]
    exact ⟨.triple u v x y z hv, rfl, rfl⟩

theorem pages_card_of_opposite {b : Book V} {e : Sym2 V}
    (hop : b.opposite = some e) : b.pages.card = 2 := by
  rw [b.pages_card]
  cases b <;> simp_all [Book.opposite, Book.pageCount]

end Book

variable [DecidableEq V] {I : Type*} [Fintype I]

/-- The union of the actual per-book covers, counting repeated edges only once. -/
def bookFamilyCover (books : I → Book V) : Finset (Sym2 V) :=
  univ.biUnion (fun i => (books i).cover)

theorem bookFamilyCover_covers (books : I → Book V)
    (F : Finset (Finset (Sym2 V))) (htri : ∀ T ∈ F, IsTriangle T)
    (hmeet : ∀ T ∈ F, ∃ i, ∀ U ∈ (books i).pages, ¬ Disjoint T U) :
    IsCover F (bookFamilyCover books) := by
  intro T hT
  obtain ⟨i, hi⟩ := hmeet T hT
  obtain ⟨e, he⟩ := (books i).meets_cover_of_not_disjoint (htri T hT) hi
  exact ⟨e, mem_inter.mpr ⟨(mem_inter.mp he).1,
    mem_biUnion.mpr ⟨i, mem_univ _, (mem_inter.mp he).2⟩⟩⟩

theorem bookFamilyCover_card (books : I → Book V) :
    (bookFamilyCover books).card + (∑ i, (books i).pages.card) ≤
      4 * Fintype.card I := by
  have hu : (bookFamilyCover books).card ≤ ∑ i, (books i).cover.card :=
    card_biUnion_le
  have hs : (∑ i, (books i).cover.card) + (∑ i, (books i).pages.card) ≤
      4 * Fintype.card I := by
    rw [← sum_add_distrib]
    calc
      (∑ i, ((books i).cover.card + (books i).pages.card)) ≤ ∑ _i : I, 4 :=
        sum_le_sum (fun i _ => (books i).cover_card_add_pages_card_le_four)
      _ = 4 * Fintype.card I := by simp [Nat.mul_comm]
  omega

/-- Represent each page family as a book and combine the book covers. -/
theorem exists_cover_of_small_common_spine_books
    (F : Finset (Finset (Sym2 V))) (pages : I → Finset (Finset (Sym2 V)))
    (hne : ∀ i, (pages i).Nonempty) (hcard : ∀ i, (pages i).card ≤ 3)
    (hpages : ∀ i T, T ∈ pages i → IsTriangle T)
    (hspine : ∀ i, ∃ e, ∀ T ∈ pages i, e ∈ T)
    (htri : ∀ T ∈ F, IsTriangle T) (hchoice : Books.EveryChoiceMeets F pages) :
    ∃ C : Finset (Sym2 V), IsCover F C ∧
      C.card + (∑ i, (pages i).card) ≤ 4 * Fintype.card I := by
  classical
  choose spine hs using hspine
  have hb (i : I) : ∃ b : Book V, b.pages = pages i ∧ b.spine = spine i :=
    Book.exists_representation (pages i) (spine i) (hne i) (hcard i) (hpages i) (hs i)
  choose books hbpages hbspine using hb
  refine ⟨bookFamilyCover books, ?_, ?_⟩
  · apply bookFamilyCover_covers books F htri
    intro T hT
    obtain ⟨i, hi⟩ := Books.exists_book_all_pages_meet hchoice hT
    exact ⟨i, by simpa only [hbpages i] using hi⟩
  · simpa only [hbpages] using bookFamilyCover_card books

end Tuza
