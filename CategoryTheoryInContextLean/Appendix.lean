import CategoryTheoryInContextLean.Section_1_1

/-!
# Category Theory in Context — приложение

В этом файле — дополнительный материал и примеры, которых нет в книге, но которые
могут быть полезны для дальнейшего изучения; используются определения из книги.
-/

namespace CategoryInContext
open Category

def Posetal (a : Type*) [C : Category a] : Prop :=
  ∀ (X Y : a), Subsingleton (C.Hom X Y)

/-
Категория с двумя объектами (Fin 2) и двумя различными морфизмами из 0 в 1

      f
    ⟿⟿⟿⟿
  0 ⟿⟿⟿⟿ 1
      g

где f, g : Fin 2 — два различных морфизма из 0 в 1
-/
def TwoMorphismCategory : Category.{0, 0} (Fin 2) where
  Hom X Y := match X, Y with
    | 0, 1 => Fin 2
    | 0, 0 => Unit
    | 1, 1 => Unit
    | 1, 0 => Empty
  id X := (match X with
    | 0 => ()
    | 1 => ())
  comp {X Y Z} f g := match X, Y, Z with
    | 0, 0, 0 => ()
    | 0, 0, 1 => g
    | 0, 1, 1 => f
    | 1, 1, 1 => ()
  id_comp {X Y} f := by match X, Y with | 0, 0 | 0, 1 | 1, 1 => rfl
  comp_id {X Y} f := by match X, Y with | 0, 0 | 0, 1 | 1, 1 => rfl
  assoc {W X Y Z} f g h := by
    match W, X, Y, Z with
    | 0, 0, 0, 0 | 0, 0, 0, 1 | 0, 0, 1, 1 | 0, 1, 1, 1 | 1, 1, 1, 1 => rfl

example : ∃ (α : Type) (C : Category.{0, 0} α), ¬ @Posetal α C := by
  use Fin 2, TwoMorphismCategory
  intro h
  have : Subsingleton (Fin 2) := h 0 1
  exact absurd (Subsingleton.elim (0 : Fin 2) 1) (Fin.zero_ne_one)

/-
Категория с 3 объектами — показывает, что slice_over не предпорядковая.
Есть два различных морфизма из 0 в 1, и оба пути 0→1→2 и 0→2 дают одну и ту же композицию.

      f
    ⟿⟿⟿⟿
  0 ⟿⟿⟿⟿ 1 ----→ 2
    ╲ g   ╱
     ╲   ╱
      ╲ ╱
       ↓

где f, g : Fin 2 — два различных морфизма из 0 в 1
-/
def ThreeObjCategory : Category.{0, 0} (Fin 3) where
  Hom X Y := match X, Y with
    | 0, 1 => Fin 2
    | 1, 2 => Unit
    | 0, 2 => Unit
    | 0, 0 | 1, 1 | 2, 2 => Unit
    | _, _ => Empty
  id X := match X with
    | 0 => ()
    | 1 => ()
    | 2 => ()
  comp {X Y Z} f g := match X, Y, Z with
    | 0, 0, 0 => ()
    | 0, 0, 1 => g
    | 0, 0, 2 => g
    | 0, 1, 1 => f
    | 0, 1, 2 => ()
    | 0, 2, 2 => f
    | 1, 1, 1 => ()
    | 1, 1, 2 => g
    | 1, 2, 2 => f
    | 2, 2, 2 => ()
  id_comp {X Y} f := by match X, Y with | 0, 0 | 0, 1 | 0, 2 | 1, 1 | 1, 2 | 2, 2 => rfl
  comp_id {X Y} f := by match X, Y with | 0, 0 | 0, 1 | 0, 2 | 1, 1 | 1, 2 | 2, 2 => rfl
  assoc {W X Y Z} f g h := by
    match W, X, Y, Z with
    | 0, 0, 0, 0 | 0, 0, 0, 1 | 0, 0, 0, 2 | 0, 0, 1, 1 | 0, 0, 1, 2 | 0, 0, 2, 2
    | 0, 1, 1, 1 | 0, 1, 1, 2 | 0, 1, 2, 2 | 0, 2, 2, 2
    | 1, 1, 1, 1 | 1, 1, 1, 2 | 1, 1, 2, 2 | 1, 2, 2, 2
    | 2, 2, 2, 2 => rfl

example : ∃ (α : Type) (_ : Category.{0, 0} α) (c: α), ¬ @Posetal _ (slice_over c) := by
  use Fin 3, ThreeObjCategory, 2
  intro h
  letI _instCat : Category (Fin 3) := ThreeObjCategory
  let obj1 : Σ X : Fin 3, Hom X 2 := ⟨1, ()⟩
  let obj0 : Σ X : Fin 3, Hom X 2 := ⟨0, ()⟩
  have hsub : Subsingleton ((slice_over 2).Hom obj0 obj1) := h obj0 obj1
  have hall : ∀ (m : Fin 2), comp (X := 0) (Y := 1) (Z := 2) m obj1.2 = obj0.2 := by
    intro; rfl
  have : Subsingleton (Fin 2) := by
    haveI : Subsingleton {h : Hom 0 1 // h ≫ obj1.2 = obj0.2} := hsub
    constructor
    intros a b
    let sa : {h : Hom 0 1 // h ≫ obj1.2 = obj0.2} := ⟨a, hall a⟩
    let sb : {h : Hom 0 1 // h ≫ obj1.2 = obj0.2} := ⟨b, hall b⟩
    have : sa = sb := Subsingleton.elim sa sb
    injection this
  exact absurd (Subsingleton.elim (0 : Fin 2) 1) Fin.zero_ne_one

end CategoryInContext
