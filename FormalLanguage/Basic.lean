import FormalLanguage.Prelude

/-
/-- https://en.wikipedia.org/wiki/Kleene_star -/
inductive KleeneStar.{v} (Alphabet: Type v)
  /-- The empty string. -/
  | ε
  /-- Concatenate a character to the end of a string. -/
  | append (string: KleeneStar Alphabet) (character: Alphabet)

-- open KleeneStar (ε)
-- @[inherit_doc] local postfix:arg "*" => KleeneStar

namespace KleeneStar
universe v
variable {α: Type v}

instance: Star (Type v) where
  star := KleeneStar

-- instance: HConcat α* α where
--   hConcat := append

-- instance: CoeFun α* (fun _ => α → α*) where
--   coe s := append s

@[inherit_doc] infixr:67 " :: " => append

instance: Coe α α* where
  coe a := ε::a

instance: Subsingleton Empty* where
  allEq | ε, ε => rfl

example (s: Empty*): s = ε := match s with | ε => rfl
example (s: Empty*): s = ε := Subsingleton.elim s ε

/-- The direction of association follows `Nat.add` instead of `List.append`. -/
def concat (xs: α*): α* → α*
  | ε => xs
  | ys::y => concat xs ys :: y

instance: Concat α* where
  concat := concat

end KleeneStar
-/

-- /-- Kleene star. -/
-- @[reducible] instance: Star (Type _) where
--   star := List

-- instance {α}: HAppend α* α* α* where
--   hAppend := .append

/-- https://en.wikipedia.org/wiki/Abstract_family_of_languages#Formal_definitions -/
class LanguageFamily.{u,v} (Λ: Type u) where
  {Alphabet: Type v}
  accept: List Alphabet → Λ → Prop
  -- nontrivial: ∃ (s: Alphabet*) (L: Λ), accept s L

namespace LanguageFamily
universe u
variable {Λ: Type u} [LanguageFamily Λ]

protected abbrev String := List (Alphabet Λ)

-- instance: Subset Λ where
--   mem := accept

section
universe v
variable (α: Type v)

instance Full: LanguageFamily (Singleton (List α)) where
  Alphabet := α
  accept _ _ := True

instance Empty: LanguageFamily (Singleton Empty) where
  Alphabet := α
  accept _ _ := False

instance Singletons: LanguageFamily (List α) where
  accept := Eq

end

end LanguageFamily
