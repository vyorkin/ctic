import Mathlib.Data.Matrix.Mul  -- используйте #min_imports для обновления

/-!
# Category Theory in Context — раздел 1.1

Вводим базовое определение категории и примеры из разных областей математики.
Также определяем изоморфизмы, группоиды и подкатегории.
-/

-- чтобы избежать конфликта имён с Mathlib.CategoryTheory.Category
namespace CategoryInContext

/--
Категория состоит из набора объектов и морфизмов между ними.
Морфизмы можно композировать, и для каждого объекта есть тождественный морфизм.
Композиция ассоциативна, а тождественные морфизмы — единицы композиции.

Замечание: небольшое отступление от определения 1.1 книги — здесь `Hom` задан как
семейство типов, индексированное парой объектов; в книге вместо этого один общий
тип морфизмов с функциями область/область значений.

определение 1.1.1
используем α вместо Obj, следуя стилю mathlib:
https://leanprover-community.github.io/contribute/style.html
-/
class Category (α : Type*) where
  -- объекты
  -- морфизмы
  Hom : α → α → Type*
  -- тождественный морфизм
  id : (X : α) → Hom X X
  -- композиция морфизмов
  -- используем запись слева направо, чтобы совпадать с mathlib,
  -- тогда как в книге принята запись справа налево, как для обычных функций
  comp : {X Y Z : α} → Hom X Y → Hom Y Z → Hom X Z
  -- утверждения / законы
  id_comp : ∀ {X Y : α} (f : Hom X Y), comp (id X) f = f
  comp_id : ∀ {X Y : α} (f : Hom X Y), comp f (id Y) = f
  assoc : ∀ {W X Y Z : α} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    comp (comp f g) h = comp f (comp g h)

-- используем ≫ вместо ∘, чтобы совпадать с mathlib.
scoped infixr:80 " ≫ " => Category.comp -- набирается как \gg

universe u
-- по сути аналог Set из книги, но здесь мы работаем с типами Lean.
instance Category.Type : Category (Type u) where
  Hom X Y := X → Y
  id _ x := x
  comp f g := g ∘ f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

-- пример 1.1.3.i
-- отличие от книги: здесь берутся подмножества (Set) одного фиксированного типа X,
-- а в книге — все множества; теоретико-множественный аналог такой категории —
-- все подмножества фиксированного множества X.
instance Category.Set (α : Type*) : Category (Set α) where
  Hom X Y := X → Y
  id _ x := x
  comp f g := g ∘ f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

-- todo: добавить больше примеров из mathlib

-- пример 1.1.4.i
def Category.MatR (α : Type*) [Ring α] : Category ℕ where
  Hom n m := Matrix (Fin m) (Fin n) α
  id := 1
  comp f g := g * f
  id_comp _ := by simp
  comp_id _ := by simp
  assoc _ _ _ := by rw [Matrix.mul_assoc]

-- пример 1.1.4.ii
def Category.Monoid (α : Type*) [Monoid α] : Category Unit where
  Hom _ _ := α
  id _ := 1
  comp f g := f * g
  id_comp := by simp
  comp_id := by simp
  assoc f g h := mul_assoc f g h

-- пример 1.1.4.iii
noncomputable instance Category.Poset (α : Type*) [PartialOrder α] : Category α where
  Hom X Y := PLift (X ≤ Y) -- немного гимнастики с универсумами для перехода между Prop и Type
  id X := ⟨le_refl X⟩
  comp f g := ⟨le_trans f.down g.down⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

-- пример 1.1.4.v
-- небольшое отличие: Set заменён на Type, поскольку в Lean мы работаем в теории типов.
def Category.TrivialType (α : Type) : Category α where
  Hom _ _ := Unit
  id _ := ()
  comp _ _ := ()
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

-- определение 1.1.6 (малые категории) и 1.1.7 (локально малые категории)
-- не ясно, возможно ли вообще сформулировать это в Lean и какое определение
-- будет правильным при теоретико-типовом основании вместо теоретико-множественного.

variable {α : Type*} [Category α]

-- определение 1.1.9
-- структуру и предикат определяем отдельно — они могут пригодиться порознь
structure Category.Isomorphism (X Y : α) where
  f : Hom X Y
  inv : Hom Y X
  hom_inv_id : f ≫ inv = id X
  inv_hom_id : inv ≫ f = id Y

def Category.id_iso (X : α) : Category.Isomorphism X X :=
  { f := Category.id X
    inv := Category.id X
    hom_inv_id := by rw [Category.id_comp]
    inv_hom_id := by rw [Category.comp_id] }

def Category.IsIso {X Y : α} (f : Hom X Y) : Prop :=
  ∃ g : Hom Y X, f ≫ g = id X ∧ g ≫ f = id Y

lemma Category.iso_iff_isIso {X Y : α} (f : Hom X Y) :
  Category.IsIso f ↔ ∃ (iso : Category.Isomorphism X Y), iso.f = f := by
  constructor
  · rintro ⟨g, hg, hf⟩
    use Category.Isomorphism.mk f g hg hf
  · rintro ⟨⟨f, g, hg, hf⟩, rfl⟩
    exact ⟨g, hg, hf⟩

def Category.Isomorphic (X Y : α) := Nonempty (Isomorphism X Y)

def Category.Endomorphism (X : α) := Hom X X
def Category.Automorphism (X : α) := Isomorphism X X

-- пример 1.1.10
-- todo: добавить больше примеров из mathlib
-- пример 1.1.10.v
lemma Category.poset_trivial (α : Type) [PartialOrder α] (X Y : α) (f : Hom X Y) :
  Category.IsIso f ↔ X = Y := by
  constructor
  · intro h
    rw [Category.iso_iff_isIso] at h
    rcases h with ⟨⟨f, g, _, _⟩, rfl⟩
    have hlt : X ≤ Y := f.down
    have hgt : Y ≤ X := g.down
    exact antisymm hlt hgt
  · intro h
    subst X
    have : f = id Y := rfl
    rw [this]
    rw [iso_iff_isIso]
    use id_iso Y
    rfl

-- определение 1.1.11
def Category.Groupoid (α : Type*) [Category α] :=
  ∀ {X Y : α} (f : Hom X Y), Category.IsIso f

-- пример 1.1.12.i
def Category.group_groupoid (α : Type*) [Group α] :
  @Category.Groupoid Unit (Category.Monoid α) := by
  intro X Y f
  unfold Category.IsIso
  use (f⁻¹ : α) -- по какой-то причине нужно явное приведение типа
  simp [Category.Monoid]

-- определение 1.1.13
-- снова из-за теоретико-типового основания: подкатегорию задаём как отображение в Prop
structure Category.Subcategory (α : Type*) [Category α] where
  obj : α → Prop
  hom : {X Y : α} → Hom X Y → Prop
  id_mem : ∀ {X}, obj X → hom (Category.id X)
  comp_mem : ∀ {X Y Z} {f : Hom X Y} {g : Hom Y Z},
    obj X → obj Y → obj Z → hom f → hom g → hom (f ≫ g)

-- Задаём отношение включения между подкатегориями через импликацию в Prop
def Category.Subcategory.subset {α : Type*} [Category α] (S T : Subcategory α) : Prop :=
  (∀ X, S.obj X → T.obj X) ∧
  (∀ {X Y} (f : Hom X Y), S.hom f → T.hom f)

-- Переопределяем нотацию ⊆
instance {α : Type*} [Category α] : HasSubset (Category.Subcategory α) where
  Subset := Category.Subcategory.subset

-- этого нет в книге
def Category.full_subcategory (α : Type*) [Category α] : Subcategory α where
  obj _ := True
  hom _ := True
  id_mem _ := trivial
  comp_mem _ _ _ _ _ := trivial

def Category.empty_subcategory (α : Type*) [Category α] : Subcategory α where
  obj _ := False
  hom _ := False
  id_mem := by intros; contradiction
  comp_mem := by intros; contradiction

lemma Category.empty_subcategory_subset {α : Type*} [Category α] :
  empty_subcategory α ⊆ full_subcategory α := by
  constructor
  · intro X h; contradiction
  · intros X Y f h; contradiction

-- лемма 1.1.13 и упражнение 1.1.ii
def Category.maximal_subgroupoid {α : Type*} [Category α] : Subcategory α where
  obj X := True
  hom f := Category.IsIso f
  id_mem x := by sorry
  comp_mem _ _ _ hf hg := by sorry

-- упражнение 1.1.i
theorem Category.pair_inverse_iso {X Y : α} (f : Hom X Y) (g : Hom Y X) (h : Hom Y X)
  (hg : f ≫ g = id X) (hf : h ≫ f = id Y) : g = h ∧ IsIso f := by sorry

theorem inv_unique_iso : ∀ {A B : α} {iso1 iso2 : Category.Isomorphism A B},
      iso1.f = iso2.f → iso1.inv = iso2.inv := by sorry

-- упражнение 1.1.iii.i
def Category.slice_under (c : α) : Category (Σ X : α, Hom c X) where
  Hom := fun ⟨X, f⟩ ⟨Y, g⟩ => {h : Hom X Y // f ≫ h = g}
  id := fun ⟨X, f⟩ => ⟨Category.id X, by rw [Category.comp_id]⟩
  comp := fun ⟨k, hk⟩ ⟨l, hl⟩ => ⟨ comp k l, by
      rw [← Category.assoc]
      rw [hk, hl]
    ⟩
  id_comp := by sorry
  comp_id := by sorry
  assoc := by sorry

def Category.slice_over (c : α) : Category (Σ X : α, Hom X c) where
  Hom := fun ⟨X, f⟩ ⟨Y, g⟩ => {h : Hom X Y // h ≫ g = f}
  id := fun ⟨X, f⟩ => ⟨Category.id X, by rw [Category.id_comp]⟩
  comp := fun ⟨k, hk⟩ ⟨l, hl⟩ => ⟨ k ≫ l, by
      rw [Category.assoc]
      rw [hl, hk]
    ⟩
  id_comp := by sorry
  comp_id := by sorry
  assoc := by sorry

end CategoryInContext
