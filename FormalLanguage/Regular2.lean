import FormalLanguage.Prelude
-- import FormalLanguage.Basic
import SoftwareFoundations.Lemma

/-!
`u` is the universe level for the type of alphabet `α` in the regular language  used throughout this file.
-/
universe u

/-- https://en.wikipedia.org/wiki/Regular_language#Formal_definition
`α` is the type of alphabet allowed in the regular language. We make it  universe-polymorphic. -/
inductive RegExp (α: Type u)
  /-- Matches nothing. -/
  | protected nothing
  /-- Empty string matcher. -/
  | ε
  | protected single (a: α)
  | protected append (r r': RegExp α)
  | protected union (r r': RegExp α)
  | protected star (r: RegExp α)

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
  | append {s r s' r'}: accept s r → accept s' r' → accept (s ++ s') (r ++ r')
  | unionL {s r r'}: accept s r → accept s (r ∪ r')
  | unionR {r s r'}: accept s r' → accept s (r ∪ r')
  | starEmpty {r}: accept [] r*
  | starAppend {s s' r}: accept s r → accept s' r* → accept (s ++ s') r*

-- export accept (empty single append unionL unionR starEmpty starAppend)
open accept

@[inherit_doc] infix:50 " =~ " => accept

instance: Setoid (RegExp α) where
  r r r' := ∀ s, s =~ r ↔ s =~ r'
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

/- If `r` matches `s`, and `r'` matches `s'`, then `r ⬝ r'` matches `s ++ s'`.-/
example {s s': List α} {r r': RegExp α}
  : s =~ r → s' =~ r' → s ++ s' =~ r ++ r' := append

/-- If at least one of `r` and `r'` matches `s`, then `r ∪ r'` matches `s`. -/
example {s: List α} {r r': RegExp α}: s =~ r ∨ s =~ r' → s =~ r ∪ r'
  | h => h.elim unionL unionR

/-- Finally, if we can write some string `s` as the concatenation of a sequence 
of strings `s = s₁ ++ ... ++ sₖ`, and the expression `r` matches each one of 
the strings `sᵢ`, then `r*` matches `s`. In particular, the sequence of 
strings may be empty, so `r*` always matches the empty string `[]` no matter 
what `r` is. -/
theorem starAppend_fold (r: RegExp α)
  : (ss: List (List α)) → (∀ s, s ∈ ss → s =~ r) → ss.foldl .append [] =~ r*
  | [], _ => starEmpty -- [] ∈ r*
  | s::ss, h =>
    have hs := h s (.head _)
    have hss := starAppend_fold r ss fun s' hs' => h s' (.tail _ hs')
    List.foldl_append_cons .. ▸ starAppend hs hss

/-!
Basics facts regarding `RegExp.accept`.
-/
section
variable {a: α} {s: List α} {r: RegExp α}

theorem accept_empty: s =~ ε → s = []
  | empty => rfl

theorem accept_single: s =~ a → s = [a]
  | single => rfl

theorem nil_of_accept_single: a::s =~ a → s = []
  | h => match s, accept_single h with | [], rfl => rfl

theorem nothing_star: s =~ ∅* → s = []
  | starEmpty => rfl

theorem star_closure: s =~ r → s =~ r*
  | h => calc s = s ++ [] := s.append_nil.symm
              _ =~ r* := starAppend h starEmpty

theorem starRec {motive: ∀ {s}, s =~ r* → Prop}
  (base: motive starEmpty)
  (ind: ∀ {s s'}, (h: s =~ r) → (h': s' =~ r*) → motive h' → motive (starAppend h h'))
  {s} (h: s =~ r*): motive h
:= by
  generalize er: r* = r; rw [er] at h
  induction h
  case empty | single | append | unionL | unionR => exact nomatch er
  case starEmpty => exact base
  case starAppend s' s'' _ h' h'' _ ih =>
    cases er; cases s'
    . case nil => exact ih h rfl
    . case cons s' _ => exact ind h' h'' (ih h'' rfl)
  -- -- Cannot apply structural recursion.
  -- | starEmpty => base
  -- | starAppend h h' => ind h h' (starRec base ind h')

theorem star_append {s s': List α}: s =~ r* → s' =~ r* → s ++ s' =~ r*
  | h, h' => by
    induction h using starRec with
    | base => exact h'
    | ind h _ ih => exact List.append_assoc .. ▸ starAppend h ih

/-- https://github.com/kolya-vasiliev/logical-foundations-2018/blob/1486b6748963514bc281672a93d408ac830ae0d0/IndProp.v#L2312 -/
theorem cons_accept_star
  : a::s =~ r* → ∃ s' s'', s = s' ++ s'' ∧ a::s' =~ r ∧ s'' =~ r*
:= by
  generalize et: a::s = t
  intros h
  induction h using starRec
  case base => exact nomatch et
  case ind s₁ s₂ h h' ih =>
    cases s₁
    . case nil => exact ih et
    . case cons s₁ => cases et; exact ⟨s₁, s₂, rfl, h, h'⟩

theorem starConsRec {motive: ∀ {s}, s =~ r* → Prop}
  (base: motive starEmpty)
  (ind: ∀ {a s s'}, (h: a::s =~ r) → (h': s' =~ r*) → motive h' → motive (starAppend h h'))
  {s} (h: s =~ r*): motive h
:= match s with
  | [] => base
  | _::s =>
    match s, cons_accept_star h with
    | _, ⟨_, _, rfl, h, h'⟩ => ind h h' (starConsRec base ind h')
termination_by _ => s.length

theorem empty_star (h: s =~ ε*): s = [] := by
  induction h using starConsRec with
  | base => rfl
  | ind h _ ih => rw [ih, accept_empty h]; rfl

theorem star_star (h: s =~ r**): s =~ r* := by
  induction h using starConsRec with
  | base => exact starEmpty
  | ind h _ ih => exact star_append h ih

example: (∀ {s}, s =~ r* → s = []) → ∀ {s}, s =~ r** → s = []
  | h, _, h' => h (star_star h')

theorem single_accept_star (h: [a] =~ r*): [a] =~ r := by
  generalize e: [a] = s at h
  induction h using starConsRec
  case base => exact nomatch e
  case ind s s' h _ _ =>
    rw [List.cons_append] at e; generalize et: s ++ s' = t at e
    cases e; rw [(List.nil_of_append_eq_nil et).2, List.append_nil]; exact h

/-- `re₁ ++ re₂` matches string `s` iff `s = s₁ ++ s₂`, where `s₁` matches 
`re₁` and `s₁` matches `re₁`. -/
theorem app_exists (s: List α) (re₁ re₂: RegExp α)
  : s =~ re₁ ++ re₂ ↔ ∃ s₁ s₂, s = s₁ ++ s₂ ∧ s₁ =~ re₁ ∧ s₂ =~ re₂
:= .intro
  fun | append hs₁ hs₂ => ⟨_, _, rfl, hs₁, hs₂⟩
  fun ⟨_, _, e, hs₁, hs₂⟩ => e ▸ append hs₁ hs₂

/-- `s` matches `Union re₁ re₂` iff `s` matches `re₁` or `s` matches `re₁`. -/
theorem union_disj (s: List α) (re₁ re₂: RegExp α)
  : s =~ re₁ ∪ re₂ ↔ s =~ re₁ ∨ s =~ re₂
:= ⟨fun | unionL h => .inl h | unionR h => .inr h, (Or.elim · unionL unionR)⟩

instance match_empty: (r: RegExp α) → Decidable ([] =~ r)
  | .nothing => isFalse (accept_nothing _)
  | ε => isTrue empty
  | (a: α) => isFalse (nomatch accept_single ·)
  | r ++ r' =>
    match match_empty r, match_empty r' with
    | isTrue h, isTrue h' => isTrue (append h h')
    | isFalse hn, _ => isFalse fun h =>
      have ⟨_, _, e, hs, _⟩ := (app_exists [] r r').mp h
      hn <| (List.nil_of_append_eq_nil e.symm).1 ▸ hs
    | _, isFalse hn => isFalse fun h =>
      have ⟨_, _, e, _, hs⟩ := (app_exists [] r r').mp h
      hn <| (List.nil_of_append_eq_nil e.symm).2 ▸ hs
  | r ∪ r' =>
    match match_empty r, match_empty r' with
    | isFalse hn, isFalse hn' => isFalse fun h =>
      ((union_disj [] r r').mp h).elim hn hn'
    | isTrue h, _ => isTrue (unionL h)
    | _, isTrue h => isTrue (unionR h)
  | _* => isTrue starEmpty

/--
[Brzozowski derivative](https://en.wikipedia.org/wiki/Brzozowski_derivative)
-/
def derive (a: α): RegExp α → RegExp α
  | .nothing | ε => ∅
  | (b: α) => if a = b then ε else ∅
  | r ++ r' => (derive a r ++ r') ∪ if [] =~ r then derive a r' else ∅
  | r ∪ r' => derive a r ∪ derive a r'
  | r* => derive a r ++ r*


namespace derive
variable {a b: α} {s: List α}

example: derive a a = ε := if_pos rfl
example: [] =~ derive a a :=
  suffices derive a a = ε from this ▸ empty; if_pos rfl
example: a ≠ b → derive a b = ∅ := (if_neg ·)

theorem mp {a: α} {s: List α} {r: RegExp α}: a::s =~ r → s =~ derive a r := by
  induction r generalizing s with
  | nothing => exact False.elim ∘ (accept_nothing _)
  | ε => exact (nomatch accept_empty ·)
  | single b => exact fun h =>
    if e: a = b then
      match s, accept_single h with
      | _, rfl => trans empty (if_pos rfl).symm
      --suffices derive a a = ε from this ▸ empty; if_pos rfl
    else
      match accept_single h with | rfl => absurd rfl e
  | append r r' ih ih' => exact fun h =>
    have ⟨s₁, _, e, h₁, h₂⟩ := (app_exists ..).mp h
    match s₁ with
    | [] =>
      if h: [] =~ r
      then have := ih' (trans e h₂); unionR (trans this (if_pos h).symm)
      else absurd h₁ h
    | x::xs => match a, x, s, e with | _, _, _, rfl => unionL (append (ih h₁) h₂)
  | union r r' ih ih' => exact fun h =>
    ((union_disj ..).mp h).elim (unionL ∘ ih) (unionR ∘ ih')
  | star r ih => exact fun h =>
    have ⟨_, _, e, h, h'⟩ := cons_accept_star h; e ▸ append (ih h) h'

end derive

def is_der (a: α) (r r': RegExp α) := ∀ s, a::s =~ r ↔ s =~ r'

theorem derives (a: α) (r: RegExp α): is_der a r (derive a r)
  | s => ⟨
    match r with
    | .nothing => (absurd · (accept_nothing _))
    | ε => (nomatch accept_empty ·)
    | (b: α) => fun h =>
      if e: a = b then
        match (accept_single h).symm with
        | rfl => suffices derive b b = ε from this ▸ empty ; if_pos rfl
      else
        match accept_single h with
        | rfl => absurd rfl e
    | r ++ r' => _
    | r ∪ r' => sorry
    | r* => sorry
    , sorry⟩

instance acceptDec (s: List α) (r: RegExp α): Decidable (s =~ r) :=
  match s with
  | [] => match_empty r
  | a::s =>
    match r with
    | .nothing => isFalse (accept_nothing _)
    | ε => isFalse (nomatch accept_empty ·)
    | (b: α) =>
      match s with
      | [] =>
        if e: a = b
        then isTrue (e ▸ single)
        else isFalse fun h => e <| match accept_single h with | rfl => rfl
      | _::_ => isFalse (nomatch accept_single ·) 
    | r ++ r' => sorry
    | r ∪ r' => sorry
    | r* =>
      match acceptDec [a] r, acceptDec s r* with
      | isTrue h, isTrue h' => isTrue (starAppend h h')
      | isFalse hn, _ =>
        match s with
        | [] => isFalse (hn ∘ single_accept_star)
        | b::s => sorry
      | _, isFalse hn => sorry
      -- match s with
      -- | [] =>
      --   match acceptDec [a] r with
      --   | isTrue h => isTrue (star_closure h)
      --   | isFalse hn => isFalse (hn ∘ single_accept_star)
      -- | b::s => _
termination_by _ => (r, s)

end

/-
/-!
Setoidal facts regarding `RegExp.accept`.
-/
section
variable {r r' re'': RegExp α}

example: ∅ ++ ∅ ≠ (∅: RegExp α)
  | h => nomatch h

theorem nothing_append: ∅ ++ r ≈ ∅
  | _ => ⟨fun | append h _ => nomatch h, (nomatch ·)⟩

theorem append_nothing: r ++ ∅ ≈ ∅
  | _ => ⟨fun | append _ h => nomatch h, (nomatch ·)⟩

example: ε ++ ε ≠ (ε: RegExp α)
  | h => nomatch h

theorem empty_append: ε ++ r ≈ r
  | _ => ⟨fun | append empty h => h, append empty⟩

theorem append_empty: r ++ ε ≈ r
  | (s: List α) =>
    ⟨ fun | append h empty => List.append_nil _ ▸ h
    , fun h => s.append_nil ▸ append h empty
    ⟩

theorem append_assoc: r ++ r' ++ re'' ≈ r ++ (r' ++ re'')
  | _ =>
    ⟨ fun | append (append h h') h'' => List.append_assoc .. ▸ append h (append h' h'')
    , fun | append h (append h' h'') => List.append_assoc .. ▸ append (append h h') h''
    ⟩

theorem nothing_union: ∅ ∪ r ≈ r
  | _ => ⟨fun | unionR h => h, unionR⟩

theorem union_nothing: r ∪ ∅ ≈ r
  | _ => ⟨fun | unionL h => h, unionL⟩

theorem union_comm: r ∪ r' ≈ r' ∪ r
  | _ => ⟨mp, mp⟩
where mp {s: List α} {r r': RegExp α}: s =~ r ∪ r' → s =~ r' ∪ r
  | unionL h => unionR h | unionR h => unionL h

theorem union_assoc: r ∪ r' ∪ re'' ≈ r ∪ (r' ∪ re'')
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

theorem append_self_star: r ++ r* ≈ r* := sorry

theorem star_append {s s': List α}: s =~ r* → s' =~ r* → s ++ s' =~ r* := by
  generalize e: r* = r; intros h
  induction h with
  | empty | single | append | unionL | unionR => exact nomatch e
  | starEmpty => exact id
  | starAppend h₁ _ _ ih =>
    exact fun h => List.append_assoc .. ▸ starAppend h₁ (ih e h)

theorem star_append_self: r* ++ r* ≈ r*
  | _ =>
    ⟨ fun
      | append starEmpty h => h
      | append (starAppend h h') h'' =>
        List.append_assoc .. ▸ starAppend h (star_append h' h'')
    , append starEmpty⟩

theorem star_involution: r** ≈ r* := sorry
--   | _ => ⟨fun | starEmpty => starEmpty | starAppend .. => _, star_closure⟩
-- where mp {s: List α} {r: RegExp α}: s =~ r** → s =~ r*
--   | starEmpty => starEmpty
--   | starAppend h h' => starAppend (mp h) (mp h')

example: (r ∪ r')* ≈ r* ∪ r'* := sorry

-- := by
--   generalize e: a::as = t, e':r* = r'; intros h
--   induction h with
--   | empty | single | append | unionL | unionR => exact nomatch e'
--   | starEmpty => exact nomatch e
--   | starAppend h h' ih ih' =>
--     match e' with
--     | rfl =>

end
-/

end RegExp
