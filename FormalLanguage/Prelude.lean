class Subset.{u,v} (Collection: Type u) where
  {Element: Type v}
  mem: Element → Collection → Prop

namespace Subset
universe u
variable {Collection: Type u} [Subset Collection]

-- instance: Membership (Element Collection) Collection where
--   mem := mem

/-- The fact that `∀ x, x ∈ A → x ∈ B`. -/
def subset (A B: Collection): Prop := ∀ x, mem x A → mem x B
@[inherit_doc] infix:50 " ⊆ " => subset

instance: Setoid Collection where
  r A B := ∀ x, mem x A ↔ mem x B
  iseqv := {
    refl := fun _ _ => .rfl
    symm := fun h x => (h x).symm
    trans := fun h h' x => (h x).trans (h' x)
  }

theorem eqv_iff_subset (A B: Collection): A ≈ B ↔ A ⊆ B ∧ B ⊆ A :=
  ⟨fun h => ⟨fun x => (h x).mp, fun x => (h x).mpr⟩, fun h x => ⟨h.1 x, h.2 x⟩⟩

end Subset

inductive Singleton {α} (a: α)
  | unique

namespace Singleton
universe u
variable {α: Type u} (a: α)

instance: Inhabited (Singleton a) where
  default := .unique

instance: Subsingleton (Singleton a) where
  allEq | _, _ => rfl

end Singleton

class Star.{u} (α: Type u) where
  /-- Typically denotes Kleene star. Binds tighter than function application. -/
  star: α → α

@[inherit_doc] postfix:arg "*" => Star.star
macro_rules | `($x *)      => `(unop% Star.star $x)

-- class HConcat.{u,v} (α: Type u) (β: Type v) where
--   /-- Preserves the type of the first argument. -/
--   hConcat: α → β → α

-- @[inherit_doc, match_pattern] infixr:67 " ⬝ " => HConcat.hConcat

class Concat.{u} (α: Type u) where
  /-- The `⬝` notation follows the definition of the append operator `++`. -/
  concat: α → α → α

@[inherit_doc] infixr:67 " ⬝ " => Concat.concat

-- instance {α} [inst: Concat α]: HConcat α α where
--   hConcat := inst.concat

class Union.{u} (α: Type u) where
  /-- The `∪` notation follows the definition of the multiplication operator 
  `*`. -/
  union: α → α → α

@[inherit_doc] infixl:70 " ∪ " => Union.union
macro_rules | `($x ∪ $y)  => `(binop% Union.union $x $y)