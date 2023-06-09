import SoftwareFoundations.Lemma

/-!
`u` is the universe level for the type of alphabet `α` in the regular language 
used throughout this file.
-/
universe u

/-- `α` is the type of alphabet allowed in the regular language. We make it 
universe-polymorphic. -/
inductive RegExp (α: Type u)
  /-- Matches nothing. -/
  | protected null
  /-- Empty string matcher. -/
  | ε
  | protected char (a: α)
  | protected app (re₁ re₂: RegExp α)
  | protected union (re₁ re₂: RegExp α)
  | protected star (re: RegExp α)

/-!
We use `α` throughout the file as an implicit parameter.
-/
variable {α: Type u}

namespace RegExp
/-!
Define convenient notations for `RegExp`.
-/

/-- Write `∅` for `RegExp.emptySet`. Set `priority` as `high` to take 
precedence over the same notation for `EmptyCollection.emptyCollection`. -/
@[default_instance] instance: EmptyCollection (RegExp α) where emptyCollection := .null

open RegExp (ε)

/-- Write `a` for `RegExp.char a`. -/
instance: Coe α (RegExp α) where coe := .char

/-- In case of `0: RegExp Nat`. -/
instance {n}: OfNat (RegExp Nat) n where ofNat := n
#check (0: RegExp Nat)

/-- Write `re₁ ++ re₂` for `RegExp.app re₁ re₂`. -/
instance: Append (RegExp α) where append := .app

/-- Write `re₁ ∪ re₂` for `RegExp.union re₁ re₂`. The `∪` notation follows the 
definition of the multiplication operator `*`. -/
infixl:70 " ∪ " => RegExp.union

/-- Write `re*` for `RegExp.star re`. This postfix operator `*` binds tighter 
than function application. -/
postfix:arg "*" => RegExp.star

/-- Constructs a regular expression that matches exactly the string that it 
receives as an argument. -/
def fromStr: List α → RegExp α
  | [] => ε
  | x::xs => x ++ fromStr xs

instance: Coe (List α) (RegExp α) where coe := fromStr
#check_failure ([]: RegExp α) -- FIXME

/-- We depart slightly from standard practice in that we do not require the 
type `α` to be finite. This results in a somewhat different theory of regular 
expressions, but the difference doesn't concern us here. -/
inductive Accept: List α → RegExp α → Prop
  | empty: Accept [] ε
  | char {x}: Accept [x] x
  | app {s₁ re₁ s₂ re₂}
    : Accept s₁ re₁ → Accept s₂ re₂ → Accept (s₁ ++ s₂) (re₁ ++ re₂)
  | unionL {s₁ re₁ re₂}: Accept s₁ re₁ → Accept s₁ (re₁ ∪ re₂)
  | unionR {re₁ s₂ re₂}: Accept s₂ re₂ → Accept s₂ (re₁ ∪ re₂)
  | starEmpty {re}: Accept [] re*
  | starApp {s₁ s₂ re}
    : Accept s₁ re → Accept s₂ re* → Accept (s₁ ++ s₂) re*

export Accept (empty char app unionL unionR starEmpty starApp)

instance: Membership (List α) (RegExp α) where mem := Accept

/-- The fact that `∀ s, s ∈ re₁ → s ∈ re₂`. -/
def sublanguage (re₁ re₂: RegExp α): Prop := ∀ s, s ∈ re₁ → s ∈ re₂
@[inherit_doc] infix:50 " ⊆ " => sublanguage

def eqv (re₁ re₂: RegExp α) := ∀ s, s ∈ re₁ ↔ s ∈ re₂

instance: Setoid (RegExp α) where
  r := eqv
  iseqv := {
    refl := fun _ _ => .rfl
    symm := fun h s => (h s).symm
    trans := fun h₁ h₂ s => (h₁ s).trans (h₂ s)
  }

example (re: RegExp α): ∅ ++ re ≈ ∅ := sorry
example (re: RegExp α): re ++ ∅ ≈ ∅ := sorry
example (re: RegExp α): ε ++ re ≈ re := sorry
example (re: RegExp α): re ++ ε ≈ re := sorry
example (re: RegExp α): ∅ ∪ re ≈ re := sorry
example (re: RegExp α): re ∪ ∅ ≈ re := sorry
example (re₁ re₂: RegExp α): re₁ ∪ re₂ ≈ re₂ ∪ re₁ := sorry
example: ∅* ≈ @ε α := sorry
  -- | s => ⟨
  --   fun
  --     | starApp hs₁ _ => ((null_matches_none _).mp hs₁).elim
  --     | starEmpty => sorry
  --   , MStar1⟩
example: ε* ≈ @ε α := sorry
  -- | s => ⟨
  --   let rec mp {s: List α}: s ∈ emptyStr* → s ∈ emptyStr
  --     | starApp hs₁ hs₂ =>
  --       have := mp hs₂
  --       match hs₁, this with | empty, empty => empty
  --     | starEmpty => empty
  --   mp
  --   , MStar1⟩

/-!
Here we verify the 6 informal rules for `Accept`.
-/

/-- `∅` does not match any string. -/
example (s: List α): s ∉ ∅ := (nomatch ·)

/-- `RegExpε` matches the empty string `[]`. -/
example: @List.nil α ∈ ε := empty

/-- `a` matches the one-character string `[a]`. -/
example (a: α): [a] ∈ (a: RegExp α) := char

/- If `re₁` matches `s₁`, and `re₂` matches `s₂`, then `re₁ ++ re₂` matches 
`s₁ ++ s₂`.-/
example {s₁ s₂: List α} {re₁ re₂: RegExp α}
  : s₁ ∈ re₁ → s₂ ∈ re₂ → s₁ ++ s₂ ∈ re₁ ++ re₂ := app

/-- If at least one of `re₁` and `re₂` matches `s`, then `re₁ ∪ re₂` matches 
`s`. -/
example {s: List α} {re₁ re₂: RegExp α}: s ∈ re₁ ∨ s ∈ re₂ → s ∈ re₁ ∪ re₂
  | h => h.elim unionL unionR

/-- Finally, if we can write some string `s` as the concatenation of a sequence 
of strings `s = s₁ ++ ... ++ sₖ`, and the expression `re` matches each one of 
the strings `sᵢ`, then `re*` matches `s`. In particular, the sequence of 
strings may be empty, so `re*` always matches the empty string `[]` no matter 
what `re` is. -/
theorem starApp_fold (re: RegExp α)
  : (ss: List (List α)) → (∀ s, s ∈ ss → s ∈ re) → ss.foldl .append [] ∈ re*
  | [], _ => starEmpty -- [] ∈ re*
  | s::ss, h =>
    have hs := h s (.head _)
    have hss := starApp_fold re ss fun s' hs' => h s' (.tail _ hs')
    List.foldl_append_cons _ _ ▸ starApp hs hss

/-!
Here are some examples of `ExpMatch`.
-/

-- example: [1] ∈ (1: RegExp Nat) := char
-- example: [1, 2] ∈ (1 ++ 2: RegExp Nat) := app char char
-- example: ¬ [1, 2] ∈ 1 := by generalize e: [1, 2] = t; exact fun | char => nomatch e
-- example: [1, 2, 3] ∈ [1, 2, 3] := app char <| app char <| app char <| empty

theorem sub_star {re: RegExp α}: re ⊆ re*
  | s, h => s.append_nil ▸ starApp h starEmpty

/-- Lists all characters that occur in a regular expression. -/
def chars: RegExp α → List α
  | ∅ | ε => []
  | (x: α) => [x]
  | re₁ ++ re₂ | re₁ ∪ re₂ => chars re₁ ++ chars re₂
  | re* => chars re

example {re: RegExp α}: chars re* = chars re := rfl
example {re: RegExp α} {x: α}: x ∈ chars re* ↔ x ∈ chars re := ⟨id, id⟩

theorem in_re_match {s: List α} {re: RegExp α} {a: α}
  : s ∈ re → a ∈ s → a ∈ re.chars
  | h => h.rec
    (nomatch .)
    id
    (fun _ _ ih₁ ih₂ h => (List.mem_of_mem_append h).elim
      (List.mem_append_of_mem_left _ ∘ ih₁)
      (List.mem_append_of_mem_right _ ∘ ih₂)
    )
    (fun _ ih₁ => List.mem_append_of_mem_left _ ∘ ih₁)
    (fun _ ih₂ => List.mem_append_of_mem_right _ ∘ ih₂)
    (nomatch ·)
    (fun _ _ ih₁ ih₂ h => (List.mem_of_mem_append h).elim ih₁ ih₂)

/-!
### Exercise: 4 stars, standard (re_not_empty)

Write a recursive function `re_not_empty` that tests whether a regular 
expression matches some string. Prove that your function is correct.
-/

def re_not_empty: RegExp α → Bool
  | ∅ => false
  | ε | (_: α) | _* => true
  | re₁ ++ re₂ => re_not_empty re₁ && re_not_empty re₂
  | re₁ ∪ re₂ => re_not_empty re₁ || re_not_empty re₂

instance re_not_empty': (re: RegExp α) → Decidable (∃ s, s ∈ re)
  | ∅ => isFalse fun ⟨_, h⟩ => nomatch h
  | ε => isTrue ⟨_, empty⟩
  | (_: α) => isTrue ⟨_, char⟩
  | re₁ ++ re₂ =>
    match re_not_empty' re₁, re_not_empty' re₂ with
    | isTrue h₁, isTrue h₂ => isTrue <|
      have ⟨_, h₁⟩ := h₁;
      have ⟨_, h₂⟩ := h₂
      ⟨_, app h₁ h₂⟩
    | isFalse h₁, _ => isFalse fun ⟨_, app hs₁ _⟩ => h₁ ⟨_, hs₁⟩
    | _, isFalse h₂ => isFalse fun ⟨_, app _ hs₂⟩ => h₂ ⟨_, hs₂⟩
  | re₁ ∪ re₂ =>
    match re_not_empty' re₁, re_not_empty' re₂ with
    | isTrue h₁, _ => isTrue <| have ⟨s, h₁⟩ := h₁; ⟨s, unionL h₁⟩
    | _, isTrue h₂ => isTrue <| have ⟨s, h₂⟩ := h₂; ⟨s, unionR h₂⟩
    | isFalse h₁, isFalse h₂ => isFalse fun
      | ⟨s, unionL h⟩ => h₁ ⟨s, h⟩
      | ⟨s, unionR h⟩ => h₂ ⟨s, h⟩
  | _* => isTrue ⟨_, starEmpty⟩

/- FIXME
theorem re_not_empty_correct
  : (re: RegExp α) → re_not_empty re = (re_not_empty' re).decide
  | ∅ | ε | (_: α) | _* => rfl
  | re₁ ++ re₂ => by decide
    -- unfold decide; unfold re_not_empty'; simp
    -- have h₁ := re_not_empty_correct re₁
    -- have h₂ := re_not_empty_correct re₂
  | re₁ ∪ re₂ => _
-/
-- (** [] *)

theorem star_app {s₁ s₂: List α} {re: RegExp α}
  : s₁ ∈ re* → s₂ ∈ re* → s₁ ++ s₂ ∈ re*
:= by
  generalize e: re* = r; intros h
  induction h with
  | empty | char | app | unionL | unionR => exact nomatch e
  | starEmpty => exact id
  | starApp h₁ _ _ ih =>
    exact fun h => List.append_assoc _ _ _ ▸ starApp h₁ (ih e h)

/-!
### Exercise: 5 stars, advanced (weak_pumping)

One of the first really interesting theorems in the theory of regular 
expressions is the so-called _pumping lemma_, which states, informally, that 
any sufficiently long string `s` matching a regular expression `re` can be 
"pumped" by repeating some middle section of `s` an arbitrary number of times 
to produce a new string also matching `re`.

To get started, we need to define "sufficiently long." Since we are working in 
a constructive logic, we actually need to be able to calculate, for each 
regular expression `re`, the minimum length for strings `s` to guarantee 
"pumpability."
-/

/-- A.k.a., pumping length, pumping constant. -/
def length: RegExp α → Nat
  | ∅ | ε => 1
  | (_: α) => 2
  | re₁ ++ re₂ | re₁ ∪ re₂ => length re₁ + length re₂
  | re* => re.length

/-!
You may find these lemmas about the pumping constant useful when proving the 
pumping lemma below.
-/

theorem length_pos: (re: RegExp α) → re.length >= 1
  | ∅ | ε => .refl
  | (_: α) => .step .refl
  | re₁ ++ _ | re₁ ∪ _ => Nat.le_trans (length_pos re₁) (Nat.le_add_right _ _)
  | re* => length_pos re

-- theorem pumping_constant_0_false (re: RegExp α): re.length ≠ 0 :=
--   Nat.not_eq_zero_of_lt (pumping_constant_pos re)

theorem napp_star {s₁ s₂: List α} {re: RegExp α}
  : {m: Nat} → s₁ ∈ re → s₂ ∈ re* → s₁^m ++ s₂ ∈ re*
  | 0, _, h₂ => h₂
  | .succ _, h₁, h₂ => List.append_assoc _ _ _ ▸ starApp h₁ (napp_star h₁ h₂)

/-!
The pumping lemma itself says that, if `s ∈ re` and if the length of `s` is at 
least the pumping constant of `re`, then `s` can be split into three substrings 
`s₁ ++ s₂ ++ s₃` in such a way that `s₂` can be repeated any number of times 
and the result, when combined with `s₁` and `s₃`, will still match `re`. Since 
`s₂` is also guaranteed not to be the empty string, this gives us a 
(constructive!) way to generate strings matching `re` that are as long as we 
like.

Now here is the usual version of the pumping lemma. In addition to requiring 
that `s₂ ≠ []`, it also requires that `s₁.length + s₂.length ≤ re.length`.
-/

theorem pumping {s: List α} {re: RegExp α}
  : s ∈ re → re.length ≤ s.length → ∃ s₁ s₂ s₃,
    s = s₁ ++ s₂ ++ s₃ ∧
    s₂ ≠ [] ∧
    s₁.length + s₂.length ≤ re.length ∧
    ∀ m: Nat, s₁ ++ s₂^m ++ s₃ ∈ re
  | h => h.rec
    (nomatch ·)
    (nomatch ·)
    (fun {t₁ re₁ t₂ re₂} ht₁ ht₂ ih₁ ih₂ hl =>
      (Nat.add_pigeon (List.length_append _ _ ▸ hl)).elim
      (fun hl₁ =>
        have ⟨s₁, s₂, s₃, happ, hnnil, hp, h⟩ := ih₁ hl₁
        ⟨s₁, s₂, s₃ ++ t₂
        , List.append_assoc _ _ _ ▸ congrArg (· ++ t₂) happ, hnnil
        , trans hp (Nat.le_add_right _ _)
        , fun m => List.append_assoc _ _ _ ▸ app (h m) ht₂⟩
      )
      (fun hl₂ =>
        have ⟨s₁, s₂, s₃, happ, hnnil, hp, h⟩ := ih₂ hl₂
        ⟨t₁ ++ s₁, s₂, s₃
        , by rw [happ]; simp only [List.append_assoc], hnnil
        , sorry
        , fun m =>
          suffices t₁ ++ (s₁ ++ s₂^m ++ s₃) = t₁ ++ s₁ ++ s₂^m ++ s₃
          from this ▸ app ht₁ (h m)
          by simp only [List.append_assoc]
        ⟩
      )
    )
    (fun _ ih₁ hl =>
      have ⟨_, _, _, happ, hnnil, hp, h⟩ := ih₁ (trans (Nat.le_add_right _ _) hl)
      ⟨_, _, _, happ, hnnil, trans hp (Nat.le_add_right _ _), fun m => unionL (h m)⟩
    )
    (fun _ ih₂ hl =>
      have ⟨_, _, _, happ, hnnil, hp, h⟩ := ih₂ (trans (Nat.le_add_left _ _) hl)
      ⟨_, _, _, happ, hnnil, trans hp (Nat.le_add_left _ _), fun m => unionR (h m)⟩
    )
    (fun hl => nomatch Nat.le_trans (length_pos _) hl)
    (fun {s₁ _ _} hs₁ hs₂ _ ih₂ hl =>
      match s₁ with
      | [] => ih₂ hl
      | _::_ => ⟨[], _, _, rfl, (nomatch ·), sorry, fun _ => napp_star hs₁ hs₂⟩
    )
-- (** [] *)

/-!
## Extended Exercise: A Verified Regular-Expression Matcher

We have now defined a match relation over regular expressions and polymorphic 
lists. We can use such a definition to manually prove that a given regex 
matches a given string, but it does not give us a program that we can run to 
determine a match automatically.

It would be reasonable to hope that we can translate the definitions of the 
inductive rules for constructing evidence of the match relation into cases of a 
recursive function that reflects the relation by recursing on a given regex. 
However, it does not seem straightforward to define such a function in which 
the given regex is a recursion variable recognized by Coq. As a result, Coq 
will not accept that the function always terminates.

Heavily-optimized regex matchers match a regex by translating a given regex 
into a state machine and determining if the state machine accepts a given 
string. However, regex matching can also be implemented using an algorithm that 
operates purely on strings and sregexes without defining and maintaining 
additional datatypes, such as state machines. We'll implement such an 
algorithm, and verify that its value reflects the match relation.

We will implement a regex matcher that matches strings represented as 
polymorphic lists, not the `String` type specifically. The matching algorithm 
that we will implement needs to be able to test equality of elements in a given 
list, and thus needs to be given an equality-testing function, namely, 
`DecidableEq`.

The proof of correctness of the regex matcher will combine properties of the 
regex-matching function with properties of the `match` relation that do not 
depend on the matching function. We'll go ahead and prove the latter class of 
properties now. Most of them have straightforward proofs, which have been given 
to you, although there are a few key lemmas that are left for you to prove.
-/

variable [DecidableEq α]

/-- `emptyStr` only matches the empty string. -/
theorem empty_matches_eps (s: List α): s ∈ ε ↔ s = [] :=
  ⟨fun | empty => rfl, (· ▸ empty)⟩

/-- `emptyStr` matches no non-empty string. -/
theorem empty_nomatch_ne (a: α) (as: List α): a::as ∉ ε
  | h => nomatch (empty_matches_eps (a::as)).mp h

/-- `char a` matches no string that starts with a non-`a` character. -/
theorem char_nomatch_char (a b: α) (bs: List α): b ≠ a → b::bs ∉ (a: RegExp α)
  | hn => by
    generalize e: b::bs = t
    exact fun | char => hn <| match e with | rfl => rfl

/-- If `char a` matches a non-empty string, then the string's tail is empty. -/
theorem char_eps_suffix (a: α) (s: List α): a::s ∈ (a: RegExp α) ↔ s = [] :=
  .intro
    (by generalize e: a::s = t; exact fun | char => match e with | rfl => rfl)
    (· ▸ char)

/-- `re₁ ++ re₂` matches string `s` iff `s = s₁ ++ s₂`, where `s₁` matches 
`re₁` and `s₁` matches `re₁`. -/
theorem app_exists (s: List α) (re₁ re₂: RegExp α)
  : s ∈ re₁ ++ re₂ ↔ ∃ s₁ s₂, s = s₁ ++ s₂ ∧ s₁ ∈ re₁ ∧ s₂ ∈ re₂
:= .intro
  fun | app hs₁ hs₂ => ⟨_, _, rfl, hs₁, hs₂⟩
  fun ⟨_, _, e, hs₁, hs₂⟩ => e ▸ app hs₁ hs₂

/-!
### Exercise: 3 stars, standard, optional (app_ne)

`re₁ ++ re₂` matches `a::s` iff `re₁` matches the empty string and `a::s` 
matches `re₁` or `s = s₁ ++ s₂`, where `a::s₁` matches `re₁` and `s₁` matches 
`re₁`.

Even though this is a property of purely the match relation, it is a critical 
observation behind the design of our regex matcher. So (1) take time to 
understand it, (2) prove it, and (3) look for how you'll use it later.
-/

theorem app_ne (a: α) (s: List α) (re₁ re₂: RegExp α)
  : a::s ∈ re₁ ++ re₂ ↔
    [] ∈ re₁ ∧ a::s ∈ re₂ ∨
    ∃ s₁ s₂, s = s₁ ++ s₂ ∧ a::s₁ ∈ re₁ ∧ s₂ ∈ re₂
:= by
  constructor
  . case mp =>
    generalize e: a::s = t; intros h
    cases h; case app s₁ s₂ hs₁ hs₂ =>
      cases s₁
      . case nil => exact .inl ⟨hs₁, hs₂⟩
      . case cons _ s₁ => cases e; exact .inr ⟨s₁, s₂, rfl, hs₁, hs₂⟩
  . case mpr =>
    intros h
    cases h
    . case inl hs => exact app hs.1 hs.2
    . case inr h => have ⟨_, _, h, hs₁, hs₂⟩ := h; exact h ▸ app hs₁ hs₂
-- (** [] *)

/-- `s` matches `Union re₁ re₂` iff `s` matches `re₁` or `s` matches `re₁`. -/
theorem union_disj (s: List α) (re₁ re₂: RegExp α)
  : s ∈ re₁ ∪ re₂ ↔ s ∈ re₁ ∨ s ∈ re₂
:= ⟨fun
    | unionL hs₁ => .inl hs₁
    | unionR hs₂ => .inr hs₂
  , (Or.elim · unionL unionR)⟩

/-!
### Exercise: 3 stars, standard, optional (star_ne)

`a::s` matches `re*` iff `s = s₁ ++ s₂`, where `a::s₁` matches `re` and `s₁` 
matches `re*`. Like `app_ne`, this observation is critical, so understand it, 
prove it, and keep it in mind.

Hint: you'll need to perform induction. There are quite a few reasonable 
candidates for `Prop`'s to prove by induction. The only one that will work is 
splitting the `iff` into two implications and proving one by induction on the 
evidence for `a::s ∈ re*`. The other implication can be proved without 
induction.

In order to prove the right property by induction, you'll need to rephrase 
`a::s ∈ re*` to be a `Prop` over general variables, using the `remember` 
tactic.
-/

theorem star_ne (a: α) (s: List α) (re: RegExp α)
  : a::s ∈ re* ↔ ∃ s₁ s₂, s = s₁ ++ s₂ ∧ a::s₁ ∈ re ∧ s₂ ∈ re*
:= by
  constructor
  . case mp =>
    generalize e: a::s = t; intros h
    cases h
    . case starEmpty => contradiction
    . case starApp s₁ s₂ hs₁ hs₂ =>
      cases s₁
      . case nil => sorry -- ⟨[], s, rfl, _, _⟩
      . case cons _ s₁ => cases e; exact ⟨_, _, rfl, hs₁, hs₂⟩
  . case mpr => exact fun ⟨_, _, e, hs₁, hs₂⟩ => e ▸ starApp hs₁ hs₂
-- (** [] *)


/-!
The definition of our regex matcher will include two fixpoint functions. The 
first function, given regex `re`, will evaluate to a value that reflects 
whether `re` matches the empty string. The function will satisfy the following 
property:
-/

-- def refl_matches_eps (m: RegExp α → Bool) := ∀ re: RegExp α, [] ∈ re ↔ m re

-- def match_eps: RegExp α → Bool
--   | ∅ => false
--   | ε => true
--   | (a: α) => false
--   | re₁ ++ re₂ => match_eps re₁ && match_eps re₂
--   | re₁ ∪ re₂ => match_eps re₁ || match_eps re₂
--   | _* => true

-- theorem match_eps_refl: @refl_matches_eps α match_eps :=
--   let rec mp {re: RegExp α} {t: List α} (e: t = []): t ∈ re → match_eps re
--     | empty
--     | starEmpty
--     | starApp _ _ => rfl
--     | app hs₁ hs₂ =>
--       have ⟨e₁, e₂⟩ := List.nil_of_append_eq_nil e
--       have h₁ := match_eps_refl.mp e₁ hs₁
--       have h₂ := match_eps_refl.mp e₂ hs₂
--       Bool.and_eq_true _ _ ▸ And.intro h₁ h₂
--     | unionL hs₁ => match_eps_refl.mp e hs₁ ▸ Bool.true_or _
--     | unionR hs₂ => match_eps_refl.mp e hs₂ ▸ Bool.or_true _
--   let rec mpr: {re: RegExp α} → match_eps re → [] ∈ re
--     | ∅, h => nomatch h
--     | ε, _ => empty
--     | _ ++ _, h =>
--       have ⟨h₁, h₂⟩ := Bool.and_eq_true _ _ ▸ h
--       app (mpr h₁) (mpr h₂)
--     | _ ∪ _, h => (Bool.or_eq_true _ _ ▸ h).elim (unionL ∘ mpr) (unionR ∘ mpr)
--     | _*, _ => starEmpty
--   fun _ => ⟨by generalize e: [] = t; exact mp e.symm, mpr⟩


/-!
We'll define other functions that use `match_eps`. However, the only property 
of `match_eps` that you'll need to use in all proofs over these functions is 
`match_eps_refl`.

The key operation that will be performed by our regex matcher will be to 
iteratively construct a sequence of regex derivatives. For each character `a` 
and regex `re`, the derivative of `re` on `a` is a regex that matches all 
suffixes of strings matched by `re` that start with `a`. I.e., `re'` is a 
derivative of `re` on `a` if they satisfy the following relation:
-/

def is_der (a: α) (re re': RegExp α) := ∀ s, a::s ∈ re ↔ s ∈ re'

/-!
A function `d` derives strings if, given character `a` and regex `re`, it 
evaluates to the derivative of `re` on `a`. I.e., `d` satisfies the following 
property:
-/

def derives (d: α → RegExp α → RegExp α) := ∀ a re, is_der a re (d a re)

/-!
### Exercise: 3 stars, standard, optional (derive)

Define `derive` so that it derives strings. One natural implementation uses 
`match_eps` in some cases to determine if key regex's match the empty string.
-/

instance match_emps (re: RegExp α): Decidable ([] ∈ re) :=
  by generalize e: [] = t; exact mp e.symm re
where mp {s: List α} (e: s = []): (re: RegExp α) → Decidable (s ∈ re)
  | ∅ => isFalse (nomatch ·)
  | ε => isTrue (e ▸ empty)
  | (a: α) => isFalse fun | char => nomatch e
  | re₁ ++ re₂ =>
    match e.symm with
    | rfl =>
      match mp e re₁, mp e re₂ with
      | isTrue h₁, isTrue h₂ => isTrue (app h₁ h₂)
      | isFalse h₁, _ => isFalse fun h =>
        have ⟨_, _, e, hs₁, _⟩ := (app_exists [] re₁ re₂).mp h
        h₁ <| (List.nil_of_append_eq_nil e.symm).1 ▸ hs₁
      | _, isFalse h₂ => isFalse fun h =>
        have ⟨_, _, e, _, hs₂⟩ := (app_exists [] re₁ re₂).mp h
        h₂ <| (List.nil_of_append_eq_nil e.symm).2 ▸ hs₂
  | re₁ ∪ re₂ =>
    match e.symm with
    | rfl =>
      match mp e re₁, mp e re₂ with
      | isFalse h₁, isFalse h₂ => isFalse fun h =>
        ((union_disj [] re₁ re₂).mp h).elim h₁ h₂
      | isTrue h₁, _ => isTrue (unionL h₁)
      | _, isTrue h₂ => isTrue (unionR h₂)
  | _* => isTrue (e ▸ starEmpty)

instance (s: List α): Decidable (s ∈ ∅) :=
  isFalse (nomatch ·)

instance: (s: List α) → Decidable (s ∈ ε)
  | [] => isTrue empty
  | x::xs => isFalse <| by
    generalize e: x::xs = t
    exact fun | empty => nomatch e

instance (a: α): (s: List α) → Decidable (s ∈ (a: RegExp α))
  | [b] => if h: a = b then isTrue (h ▸ char) else
    isFalse <| by generalize e: [b] = t; exact fun
      | char => match e with | rfl => h rfl
  | [] => isFalse <| by generalize e: [] = t; exact fun | char => nomatch e
  | b::c::cs => isFalse <| by generalize e: b::c::cs = t; exact fun
    | char => nomatch e

def derive (a: α): RegExp α → RegExp α
  | ∅
  | ε => ∅
  | (b: α) => if a = b then ε else ∅
  | re₁ ++ re₂ => (derive a re₁ ++ re₂) ∪ if [] ∈ re₁ then derive a re₂ else ∅
  | re₁ ∪ re₂ => derive a re₁ ∪ derive a re₂
  | re* => derive a re ++ re*
-- (** [] *)

/-!
The `derive` function should pass the following tests. Each test establishes an 
equality between an expression that will be evaluated by our regex matcher and 
the final value that must be returned by the regex matcher. Each test is 
annotated with the match fact that it reflects.
-/

local instance: Coe String (List Char) where coe s := s.data

/-- `¬ ['c'] ∈ ∅` -/
theorem test_der0: ¬ [] ∈ derive 'c' ∅ := by decide

/-- `['c'] ∈ 'c'` -/
theorem test_der1: [] ∈ derive 'c' 'c' := by decide

/-- `¬ ['c'] ∈ 'd'` -/
theorem test_der2: ¬ [] ∈ derive 'c' 'd' := by decide

/-- `['c'] ∈ 'c' ++ ε` -/
theorem test_der3: [] ∈ derive 'c' (.char 'c' ++ ε) := by decide

/-- `['c'] ∈ ε ++ 'c'` -/
theorem test_der4: [] ∈ derive 'c' (ε ++ .char 'c') := by decide

/-- `['c'] ∈ 'c'*` -/
theorem test_der5: [] ∈ derive 'c' 'c'* := by decide

/-- `['c', 'd'] ∈ 'c' ++ 'd'` -/
theorem test_der6: [] ∈ derive 'd' (derive 'c' ('c' ++ 'd')) := by decide

/-- `¬ ['c', 'd'] ∈ 'd' ++ 'c'` -/
theorem test_der7: ¬ [] ∈ derive 'd' (derive 'c' ('d' ++ 'c')) := by decide

/-!
### Exercise: 4 stars, standard, optional (derive_corr)

Prove that `derive` in fact always derives strings.

Hint: one proof performs induction on `re`, although you'll need to carefully 
choose the property that you prove by induction by generalizing the appropriate 
terms.

Hint: if your definition of `derive` applies `match_eps` to a particular regex 
`re`, then a natural proof will apply `match_eps_refl` to `re` and destruct the 
result to generate cases with assumptions that the `re` does or does not match 
the empty string.

Hint: You can save quite a bit of work by using lemmas proved above. In 
particular, to prove many cases of the induction, you can rewrite a `Prop` over 
a complicated regex (e.g., `s ∈ re₁ ∪ re₂`) to a Boolean combination of 
`Prop`'s over simple regex's (e.g., `s ∈ re₁ ∨ s ∈ re₂`) using lemmas given 
above that are logical equivalences. You can then reason about these `Prop`'s 
naturally using `intro` and `destruct`.
-/
theorem derive_corr: @derives α derive := sorry
-- (** [] *)

/-!
We'll define the regex matcher using `derive`. However, the only property of 
`derive` that you'll need to use in all proofs of properties of the matcher is 
`derive_corr`.
-/

/-- A function `m` _matches regexes_ if, given string `s` and regex `re`, it 
evaluates to a value that reflects whether `s` is matched by `re`. I.e., `m` 
holds the following property: -/
def matches_regex (m: List α → RegExp α → Bool): Prop :=
  ∀ (s: List α) (re: RegExp α), s ∈ re ↔ m s re

/-!
### Exercise: 2 stars, standard, optional (regex_match)

Complete the definition of `regex_match` so that it matches regexes.
-/

def regex_match (s: List α) (re: RegExp α): Bool := sorry
-- (** [] *)

/-!
### Exercise: 3 stars, standard, optional (regex_match_correct)

Finally, prove that `regex_match` in fact matches regexes.

Hint: if your definition of `regex_match` applies `match_eps` to regex `re`, 
then a natural proof applies `match_eps_refl` to `re` and destructs the result 
to generate cases in which you may assume that `re` does or does not match the 
empty string.

Hint: if your definition of `regex_match` applies `derive` to character `x` and 
regex `re`, then a natural proof applies `derive_corr` to `x` and `re` to prove 
that `x::s ∈ re` given `s ∈ derive x re`, and vice versa.
-/

theorem regex_match_correct: @matches_regex α regex_match := sorry
-- (** [] *)

end RegExp
