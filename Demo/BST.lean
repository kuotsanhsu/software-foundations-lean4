#check LE

instance {α} [instLE: LE α] [Antisymm instLE.le]: LT α where
  lt x y := x ≤ y ∧ x ≠ y

class PartialOrder.{u} (α: Type u) extends LE α where
  refl {x: α}: x ≤ x
  antisymm {x y: α}: x ≤ y → y ≤ x → x = y
  trans {x y z: α}: x ≤ y → y ≤ z → x ≤ z

namespace PartialOrder
universe u
variable {α: Type u} [self: PartialOrder α]

instance: Antisymm self.le where
  antisymm := antisymm

end PartialOrder

inductive Tree.{u} (α: Type u)
  | leaf
  | node (key: α) (left right: Tree α)
  deriving Repr

namespace Tree
universe u
variable {α: Type u} [po: PartialOrder α]

inductive Forall (p: α → Prop): Tree α → Prop
  /-- A leaf shall satisfy whatever conditions. -/
  | leaf: Forall p leaf
  | node {key left right}
    : p key
    → left.Forall p
    → right.Forall p
    → (node key left right).Forall p

class inductive IsBST: Tree α → Prop
  | leaf: IsBST leaf
  | node {key left right}
    : left.IsBST → left.Forall (· < key)
    → right.IsBST → right.Forall (key < ·)
    → (node key left right).IsBST

variable (tree: Tree α) [tree.IsBST]

def BST (α: Type _) [PartialOrder α] := { tree: Tree α // tree.IsBST }

variable [DecidableRel po.le] [DecidableEq α]

instance (x y: α): Decidable (x < y) :=
  if h: x ≤ y then
    if e: x = y then
      isFalse (And.right · e)
    else
      isTrue ⟨h, e⟩
  else
    isFalse (h ∘ And.left)

def insert (t: BST α) (a: α): BST α :=
  match t.val with
  | leaf => ⟨node a leaf leaf, .node .leaf .leaf .leaf .leaf⟩
  | node k left right =>
    if h: a < k then
      ⟨insert left a, _⟩
    else if h': k < a then
      sorry
    else
      sorry


end Tree

example (p: Prop): p → ¬¬p | h, h' => h' h

namespace Experiment
universe u
variable (α: Type u) [LT α]

inductive BST: (α → Prop) → Type u 
  | leaf {p}: BST p
  | node {p} (key: α) (left: BST (· < key)) (right: BST (key < ·)): BST p

end Experiment

