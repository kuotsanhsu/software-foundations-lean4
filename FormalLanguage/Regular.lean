import FormalLanguage.Prelude
-- import FormalLanguage.Basic
import SoftwareFoundations.Lemma

/-!
`u` is the universe level for the type of alphabet `α` in the regular language 
used throughout this file.
-/
universe u

/-- https://en.wikipedia.org/wiki/Regular_language#Formal_definition
`α` is the type of alphabet allowed in the regular language. We make it 
universe-polymorphic. -/
inductive RegExp (α: Type u)
  /-- Matches nothing. -/
  | protected nothing
  /-- Empty string matcher. -/
  | ε
  | protected single (a: α)
  | protected append (re re': RegExp α)
  | protected union (re re': RegExp α)
  | protected star (re: RegExp α)

-- open RegExp (ε)

/-!
We use `α` throughout the file as an implicit parameter.
-/
variable {α: Type u} [DecidableEq α]

namespace RegExp
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

/-- Write `re ⬝ re'` for `RegExp.append re re'`. -/
instance: Append (RegExp α) where
  append := .append

/-- Write `re ∪ re'` for `RegExp.union re re'`. -/
@[default_instance, match_pattern] instance: Union (RegExp α) where
  union := .union

/-- Write `re*` for `RegExp.star re`. This postfix operator `*` binds tighter 
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

/-- We depart slightly from standard practice in that we do not require the 
type `α` to be finite. This results in a somewhat different theory of regular 
expressions, but the difference doesn't concern us here. -/
inductive accept: List α → RegExp α → Prop
  | empty: accept [] ε
  | single {a: α}: accept [a] a
  | append {s re s' re'}: accept s re → accept s' re' → accept (s ++ s') (re ++ re')
  | unionL {s re re'}: accept s re → accept s (re ∪ re')
  | unionR {re s re'}: accept s re' → accept s (re ∪ re')
  | starEmpty {re}: accept [] re*
  | starAppend {s s' re}: accept s re → accept s' re* → accept (s ++ s') re*

export accept (empty single append unionL unionR starEmpty starAppend)

@[inherit_doc] infix:50 " =~ " => accept

instance: Setoid (RegExp α) where
  r re re' := ∀ s, s =~ re ↔ s =~ re'
  iseqv := {
    refl := fun _ _ => .rfl
    symm := fun h s => (h s).symm
    trans := fun h h' s => (h s).trans (h' s)
  }

-- instance: LanguageFamily (RegExp α) where
--   accept := accept

/-!
Here we verify the 6 informal rules for `RegExp.accept`.
-/

/-- `∅` does not match any string. -/
theorem accept_nothing (s: List α): ¬ s =~ ∅ := (nomatch ·)

/-- `ε` matches the empty string `[]`. -/
example: [] =~ @ε α := empty

/-- `a: α` matches the one-character string `[a]`. -/
example (a: α): [a] =~ a := single

/- If `re` matches `s`, and `re'` matches `s'`, then `re ⬝ re'` matches `s ++ s'`.-/
example {s s': List α} {re re': RegExp α}
  : s =~ re → s' =~ re' → s ++ s' =~ re ++ re' := append

/-- If at least one of `re` and `re'` matches `s`, then `re ∪ re'` matches `s`. -/
example {s: List α} {re re': RegExp α}: s =~ re ∨ s =~ re' → s =~ re ∪ re'
  | h => h.elim unionL unionR

/-- Finally, if we can write some string `s` as the concatenation of a sequence 
of strings `s = s₁ ++ ... ++ sₖ`, and the expression `re` matches each one of 
the strings `sᵢ`, then `re*` matches `s`. In particular, the sequence of 
strings may be empty, so `re*` always matches the empty string `[]` no matter 
what `re` is. -/
theorem starAppend_fold (re: RegExp α)
  : (ss: List (List α)) → (∀ s, s ∈ ss → s =~ re) → ss.foldl .append [] =~ re*
  | [], _ => starEmpty -- [] ∈ re*
  | s::ss, h =>
    have hs := h s (.head _)
    have hss := starAppend_fold re ss fun s' hs' => h s' (.tail _ hs')
    List.foldl_append_cons _ _ ▸ starAppend hs hss

/-!
Basics facts regarding `RegExp.accept`.
-/
section
variable {a: α} {s: List α} {re: RegExp α}

theorem accept_empty: s =~ ε → s = []
  | empty => rfl

theorem accept_single: s =~ a → s = [a]
  | single => rfl

theorem star_closure: s =~ re → s =~ re*
  | h => calc s = s ++ [] := s.append_nil.symm
              _ =~ re* := starAppend h starEmpty

theorem empty_star: s =~ ε* → s = [] := sorry

theorem single_accept_star: [a] =~ re* → [a] =~ re := sorry
--   := aux rfl
-- where aux {s: List α} (e: [a] = s): s =~ re* → s =~ re
--   | starAppend (s := s) (s' := s') h h' =>
--     match s, s', e with
--     | [], _, rfl => _
--     | [_], _, rfl => [a].append_nil ▸ h

theorem cons_accept_star: a::s =~ re* → ∃ s' s'', s = s' ++ s'' ∧ a::s' =~ re ∧ s'' =~ re*
:= by
  generalize e: a::s = t; intros h
  match h with
  | starAppend (s := s') (s' := s'') h h' =>
    match s with
    | [] =>
      match s', s'', e with
      | [], _, rfl => exact ⟨[], [], rfl, single_accept_star h', starEmpty⟩
      | [_], _, rfl => exact ⟨[], [], rfl, h, starEmpty⟩
    | b::s => sorry

end

/-!
Setoidal facts regarding `RegExp.accept`.
-/
section
variable {re re' re'': RegExp α}

example: ∅ ++ ∅ ≠ (∅: RegExp α)
  | h => nomatch h

theorem nothing_append: ∅ ++ re ≈ ∅
  | _ => ⟨fun | append h _ => nomatch h, (nomatch ·)⟩

theorem append_nothing: re ++ ∅ ≈ ∅
  | _ => ⟨fun | append _ h => nomatch h, (nomatch ·)⟩

example: ε ++ ε ≠ (ε: RegExp α)
  | h => nomatch h

theorem empty_append: ε ++ re ≈ re
  | _ => ⟨fun | append empty h => h, append empty⟩

theorem append_empty: re ++ ε ≈ re
  | (s: List α) =>
    ⟨ fun | append h empty => List.append_nil _ ▸ h
    , fun h => s.append_nil ▸ append h empty
    ⟩

theorem append_assoc: re ++ re' ++ re'' ≈ re ++ (re' ++ re'')
  | _ =>
    ⟨ fun | append (append h h') h'' => List.append_assoc _ _ _ ▸ append h (append h' h'')
    , fun | append h (append h' h'') => List.append_assoc _ _ _ ▸ append (append h h') h''
    ⟩

theorem nothing_union: ∅ ∪ re ≈ re
  | _ => ⟨fun | unionR h => h, unionR⟩

theorem union_nothing: re ∪ ∅ ≈ re
  | _ => ⟨fun | unionL h => h, unionL⟩

theorem union_comm: re ∪ re' ≈ re' ∪ re
  | _ => ⟨mp, mp⟩
where mp {s: List α} {re re': RegExp α}: s =~ re ∪ re' → s =~ re' ∪ re
  | unionL h => unionR h | unionR h => unionL h

theorem union_assoc: re ∪ re' ∪ re'' ≈ re ∪ (re' ∪ re'')
  | _ =>
    ⟨ fun
      | unionL (unionL h) => unionL h
      | unionL (unionR h) => unionR (unionL h)
      | unionR h => unionR (unionR h)
    , fun
      | unionL h => unionL (unionL h)
      | unionR (unionL h) => unionL (unionR h)
      | unionR (unionR h) => unionR h
    ⟩

theorem nothing_star: ∅* ≈ (ε: RegExp α)
  | _ => ⟨fun | starEmpty => empty, fun | empty => starEmpty⟩

-- theorem empty_star: ε* ≈ (ε: RegExp α)
--   | s =>
--     ⟨ fun | starEmpty => empty | starAppend empty h => _
--     , star_closure
--     ⟩

theorem append_self_star: re ++ re* ≈ re* := sorry

theorem star_append {s s': List α}: s =~ re* → s' =~ re* → s ++ s' =~ re* := by
  generalize e: re* = r; intros h
  induction h with
  | empty | single | append | unionL | unionR => exact nomatch e
  | starEmpty => exact id
  | starAppend h₁ _ _ ih =>
    exact fun h => List.append_assoc _ _ _ ▸ starAppend h₁ (ih e h)

theorem star_append_self: re* ++ re* ≈ re*
  | _ =>
    ⟨ fun
      | append starEmpty h => h
      | append (starAppend h h') h'' =>
        List.append_assoc _ _ _ ▸ starAppend h (star_append h' h'')
    , append starEmpty⟩

theorem star_involution: re** ≈ re* := sorry
--   | _ => ⟨fun | starEmpty => starEmpty | starAppend _ _ => _, star_closure⟩
-- where mp {s: List α} {re: RegExp α}: s =~ re** → s =~ re*
--   | starEmpty => starEmpty
--   | starAppend h h' => starAppend (mp h) (mp h')

example: (re ∪ re')* ≈ re* ∪ re'* := sorry

-- := by
--   generalize e: a::as = t, e':re* = re'; intros h
--   induction h with
--   | empty | single | append | unionL | unionR => exact nomatch e'
--   | starEmpty => exact nomatch e
--   | starAppend h h' ih ih' =>
--     subst e'

-- instance decAcceptSingle {a: α}: Decidable ([a] =~ re) :=
--   match re with
--   | .nothing => isFalse (accept_nothing _)
--   | ε => isFalse _
--   | (b: α) =>
--     if e: a = b
--     then isTrue (e ▸ single)
--     else isFalse fun h => e <| match accept_single h with | rfl => rfl
--   | re ∪ re' => _
--   | re ++ re' => _
--   | re* => _

-- instance decAcceptStar: (s: List α) → Decidable (s =~ re*)
--   | [] => isTrue starEmpty
--   | [a] => _
--   | a::b::s => _

end

end RegExp
