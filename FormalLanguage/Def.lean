import FormalLanguage.Prelude

/-- https://en.wikipedia.org/wiki/Regular_language#Formal_definition
`α` is the type of alphabet allowed in the regular language. We make it  universe-polymorphic. -/
inductive RegExp.{u} (α: Type u)
  /-- Matches nothing. -/
  | protected nothing
  /-- Empty string matcher. -/
  | ε
  | protected single (a: α)
  | protected append (r₁ r₂: RegExp α) -- "ab"
  | protected union (r₁ r₂: RegExp α) -- "x(a|b)y"
  -- append x (append (union a b) y)
  | protected star (r: RegExp α) -- "x*": ""

export RegExp (ε)

namespace RegExp
universe u
variable {α: Type u}

/-!
Define convenient notations for `RegExp`.
-/

/-- Write `∅` for `RegExp.empty`. -/
@[default_instance] instance: EmptyCollection (RegExp α) where
  emptyCollection := .nothing

/-- Write `a: α` for `RegExp.char a`. -/
instance: Coe α (RegExp α) where
  coe := .single

/-- In case of `0: RegExp Nat`. -/
instance {n}: OfNat (RegExp Nat) n where
  ofNat := n
#check (0: RegExp Nat)

/-- Write `r ++ r'` for `RegExp.append r r'`. -/
instance: Append (RegExp α) where
  append := .append

/-- Write `r ∪ r'` for `RegExp.union r r'`. -/
@[default_instance, match_pattern] instance: Union (RegExp α) where
  union := .union

/-- Write `r*` for `RegExp.star r`. This postfix operator `*` binds tighter
than function application. -/
instance: Star (RegExp α) where
  star := .star

/-- Constructs a regular expression that matches exactly the string that it
receives as an argument. -/
def fromStr: List α → RegExp α
  | [] => ε
  | x::xs => x ++ fromStr xs

instance: Coe (List α) (RegExp α) where
  coe := fromStr
#check_failure ([]: RegExp α) -- FIXME

/-- Denoted by the Haskell operator `=~` to avoid overloading `∈` as done in
theoretical computer science; really, `∈` is way too overloaded in math. We
depart slightly from standard practice in that we do not require the type `α`
to be finite. This results in a somewhat different theory of regular
expressions, but the difference doesn't concern us here. -/
inductive accept: List α → RegExp α → Prop
  | empty: accept [] ε
  | single {a: α}: accept [a] a
  | append {s₁ r₁ s₂ r₂}
    : accept s₁ r₁ → accept s₂ r₂ → accept (s₁ ++ s₂) (r₁ ++ r₂)
  | unionL {s₁ r₁ r₂}: accept s₁ r₁ → accept s₁ (r₁ ∪ r₂)
  | unionR {r₁ s₂ r₂}: accept s₂ r₂ → accept s₂ (r₁ ∪ r₂)
  | starEmpty {r}: accept [] r*
  | starAppend {s₁ s₂ r}: accept s₁ r → accept s₂ r* → accept (s₁ ++ s₂) r*

export accept (empty single append unionL unionR starEmpty starAppend)

@[inherit_doc] infix:50 " =~ " => accept

end RegExp

-- Lean4, Coq (OCaml), Agda (Haskell)
-- Dependent type
