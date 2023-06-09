instance {α} [inst: LE α] [Antisymm inst.le]: LT α where
  lt x y := x ≤ y ∧ x ≠ y

class PartialOrder.{u} (α: Type u) extends LE α where
  refl {x: α}: x ≤ x
  antisymm {x y: α}: x ≤ y → y ≤ x → x = y
  trans {x y z: α}: x ≤ y → y ≤ z → x ≤ z

namespace PartialOrder
universe u
variable {α: Type u} [inst: PartialOrder α]

instance: Antisymm inst.le where
  antisymm := inst.antisymm

example: LT α := inferInstance

section
variable [DecidableEq α]

theorem le_iff_lt_or_eq {x y: α}: x ≤ y ↔ x < y ∨ x = y :=
  ⟨ (if e: x = y then .inr e else .inl ⟨·, e⟩)
  , (Or.elim · And.left fun | rfl => inst.refl) ⟩

end

theorem le_iff_not_gt {x y: α}: x ≤ y ↔ ¬ x > y :=
  ⟨ fun h ⟨h', e⟩ => e (inst.antisymm h' h)
  , fun h => _ ⟩

end PartialOrder

example (p q: Prop): ¬ p ∧ q → ¬p ∨ ¬q
  | h => Classical.byCases (fun hp => _) Or.inl

#check Clasical.demorg
