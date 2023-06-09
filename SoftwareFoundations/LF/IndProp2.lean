import SoftwareFoundations.LF.Poly

/-!
## Case Study: Regular Expressions

The `ev` property provides a simple example for illustrating inductive 
definitions and the basic techniques for reasoning about them, but it is not 
terribly exciting -- after all, it is equivalent to the two non-inductive 
definitions of evenness that we had already seen, and does not seem to offer 
any concrete benefit over them.

To give a better sense of the power of inductive definitions, we now show how 
to use them to model a classic concept in computer science: 
_regular expressions_.

Regular expressions are a simple language for describing sets of strings. Here, 
strings are understood as an ordered list of alphabet not restricted to the 
`String` type defined in the prelude. Their syntax is defined as follows:
-/

/-- `α` is the type of alphabet allowed in the regular language. We make it
universe-polymorphic. -/
inductive RegExp.{u} (α: Type u): Type u :=
  | emptySet
  | emptyStr
  | char (a: α)
  | app (re₁ re₂: RegExp α)
  | union (re₁ re₂: RegExp α)
  | star (re: RegExp α)

/-!
The following is the universe-polymorphic declaration of the alphabet type `α` 
that is used throughout this whole document.
-/
universe u
variable {α: Type u}

/-- Set `priority` as `high` to take precedence over the same notation for 
`EmptyCollection.emptyCollection`. -/
notation (priority := high) "∅" => RegExp.emptySet
instance: Coe α (RegExp α) where coe := .char
instance {n}: OfNat (RegExp Nat) n where ofNat := n
instance: Append (RegExp α) where append := .app
/-- The `∪` notation follows the definition of the multiplication operator `*`. 
-/
infixl:70 " ∪ " => RegExp.union
/-- This postfix operator `*` binds tighter than function application. -/
postfix:arg "*" => RegExp.star

/-!
Note that this definition is _polymorphic_: Regular expressions in `RegExp α` 
describe strings with characters drawn from `α` -- that is, lists of elements 
of `α`.

(Technical aside: We depart slightly from standard practice in that we do not 
require the type `α` to be finite.  This results in a somewhat different theory 
of regular expressions, but the difference is not significant for present 
purposes.)

We connect regular expressions and strings via the following rules, which 
define when a regular expression _matches_ some string:

- The expression `∅` (i.e., `RegExp.emptySet`) does not match any string.
- The expression `RegExp.emptyStr` matches the empty string `[]`.
- The expression `x` (i.e., `RegExp.char x`) matches the one-character string 
  `[x]`.
- If `re₁` matches `s₁`, and `re₂` matches `s₂`, then `re₁ ++ re₂` matches 
  `s₁ ++ s₂`.
- If at least one of `re₁` and `re₂` matches `s`, then `re₁ ∪ re₂` matches `s`.
- Finally, if we can write some string `s` as the concatenation of a sequence 
  of strings `s = s₁ ++ ... ++ sₖ`, and the expression `re` matches each one of 
  the strings `sᵢ`, then `re*` matches `s`. In particular, the sequence of 
  strings may be empty, so `re*` always matches the empty string `[]` no matter 
  what `re` is.

We can easily translate this informal definition into an `inductive` one as 
follows. We use the notation `s =~ re` in place of `ExpMatch s re`. (Unlike 
Coq, Lean doesn't support "reserving" the notation before the `inductive` 
definition, so we cannot use `=~` in the definition.)
-/

inductive ExpMatch: List α → RegExp α → Prop
  | empty: ExpMatch [] .emptyStr
  | char {x}: ExpMatch [x] x
  | app {s₁ re₁ s₂ re₂}
    : ExpMatch s₁ re₁ → ExpMatch s₂ re₂ → ExpMatch (s₁ ++ s₂) (re₁ ++ re₂)
  | unionL {s₁ re₁ re₂}: ExpMatch s₁ re₁ → ExpMatch s₁ (re₁ ∪ re₂)
  | unionR {re₁ s₂ re₂}: ExpMatch s₂ re₂ → ExpMatch s₂ (re₁ ∪ re₂)
  | star0 {re}: ExpMatch [] re*
  | starApp {s₁ s₂ re}
    : ExpMatch s₁ re → ExpMatch s₂ re* → ExpMatch (s₁ ++ s₂) re*

/-- The precedence of `=~` is set to that of the propositional equality `=`. -/
infix:50 " =~ " => ExpMatch

/-!
Notice that these rules are not _quite_ the same as the informal ones that we 
gave at the beginning of the section. First, we don't need to include a rule 
explicitly stating that no string matches `∅`; we just don't happen to include 
any rule that would have the effect of some string matching `∅`. (Indeed, the 
syntax of inductive definitions doesn't even _allow_ us to give such a 
"negative rule.")

Second, the informal rules for `RegExp.union` and `RegExp.star` correspond to 
two constructors each: `ExpMatch.unionL`/`ExpMatch.unionR`, and 
`ExpMatch.star0`/`ExpMatch.starApp`. The result is logically equivalent to the 
original rules but more convenient to use in Lean, since the recursive 
occurrences of `ExpMatch` are given as direct arguments to  the constructors, 
making it easier to perform induction on evidence. (The `exp_match_ex1` and 
`exp_match_ex2` exercises below ask you to prove that the constructors given in 
the inductive declaration and the ones that would arise from a more literal 
transcription of the informal rules are indeed equivalent.)

Let's illustrate these rules with a few examples.
-/

theorem reg_exp_ex1: [1] =~ 1 := .char

theorem reg_exp_ex2: [1, 2] =~ 1 ++ 2 := .app .char .char

/-!
(Notice how the last example applies `RegExp.app` to the string `[1]` directly. 
Since the goal mentions `[1, 2]` instead of `[1] ++ [2]`, Lean wouldn't be able 
to figure out how to split the string on its own.)

Using `nomatch`, we can also show that certain strings do _not_ match a regular 
expression:
-/

theorem reg_exp_ex3: ¬ [1, 2] =~ 1 := by
  generalize e: [1, 2] = t; exact fun .char => nomatch e

/-!
We can define helper functions for writing down regular expressions. The 
`reg_exp_of_list` function constructs a regular expression that matches exactly 
the list that it receives as an argument:
-/

def reg_exp_of_list: List α → RegExp α
  | [] => .emptyStr
  | x::xs => x ++ reg_exp_of_list xs

theorem reg_exp_ex4: [1, 2, 3] =~ reg_exp_of_list [1, 2, 3] :=
  .app .char <| .app .char <| .app .char <| .empty

/-!
With the following coercion instance in place, we can leave out 
`reg_exp_of_list` in `reg_exp_ex4'`.
-/

instance: Coe (List α) (RegExp α) where coe := reg_exp_of_list

theorem reg_exp_ex4': [1, 2, 3] =~ [1, 2, 3] := reg_exp_ex4

/-!
We can also prove general facts about `exp_match`. For instance, the following 
lemma shows that every string `s` that matches `re` also matches `re*`
-/

theorem MStar1 {s: List α} {re: RegExp α}: s =~ re → s =~ re*
  | h => List.append_nil s ▸ .starApp h .star0

/-!
(Note the use of `List.append_nil` to change the goal of the theorem to exactly 
the same shape expected by `ExpMatch.starApp`.)

### Exercise: 3 stars, standard (exp_match_ex1)

The following lemmas show that the informal matching rules given at the 
beginning of the chapter can be obtained from the formal inductive definition.
-/

theorem empty_is_empty (s: List α): ¬ s =~ ∅ := (nomatch ·)

theorem MUnion' {s: List α} {re₁ re₂: RegExp α}
  : s =~ re₁ ∨ s =~ re₂ → s =~ re₁ ∪ re₂
  | h => h.elim .unionL .unionR

/-!
The next lemma is stated in terms of the `fold` function from the `Poly` 
chapter: If `ss: List (List α)` represents a sequence of strings 
`[s₁, ..., sₙ]`, then `fold app ss []` is the result of concatenating them all 
together.
-/

theorem MStar' {re: RegExp α}
  : {ss: List (List α)} → (∀ s, s ∈ ss → s =~ re) → fold .append ss [] =~ re*
  | [], _ => .star0
  | x::xs, h => .starApp (h x (.head xs)) (MStar' fun s hs => h s (.tail x hs))
-- (** [] *)

/-!
Since the definition of `ExpMatch` has a recursive structure, we might expect 
that proofs involving regular expressions will often require induction on 
evidence.

For example, suppose we want to prove the following intuitive result: If a 
regular expression `re` matches some string `s`, then all elements of `s` must 
occur as character literals somewhere in `re`.

To state this as a theorem, we first define a function `re_chars` that lists 
all characters that occur in a regular expression:
-/

def re_chars: RegExp α → List α
  | ∅ | .emptyStr => []
  | (x: α) => [x]
  | re₁ ++ re₂
  | re₁ ∪ re₂ => re_chars re₁ ++ re_chars re₂
  | re* => re_chars re

/- FIXME: I added these examples. -/
example {re: RegExp α}: re_chars re* = re_chars re := rfl
example {re: RegExp α} {x: α}: x ∈ re_chars re* → x ∈ re_chars re := id
example {re: RegExp α} {x: α}: x ∈ re_chars re → x ∈ re_chars re* := id

/-- I added this theorem which is neither found in SF nor Lean's prelude. -/
theorem List.mem_of_mem_append {a: α} {ys: List α}
  : {xs: List α} → a ∈ xs ++ ys → a ∈ xs ∨ a ∈ ys
  | [], h => .inr h
  | _::xs, .head _ => .inl (.head xs)
  | x::_, .tail _ h => (mem_of_mem_append h).elim (.inl ∘ .tail x) .inr

/-!
The main theorem:
-/

theorem in_re_match {s: List α} {re: RegExp α} {x: α}
  : s =~ re → x ∈ s → x ∈ re_chars re
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
  | .emptyStr | (_: α) | _* => true
  | re₁ ++ re₂ => re_not_empty re₁ && re_not_empty re₂
  | re₁ ∪ re₂ => re_not_empty re₁ || re_not_empty re₂

instance re_not_empty': (re: RegExp α) → Decidable (∃ s, s =~ re)
  | ∅ => isFalse fun ⟨_, h⟩ => nomatch h
  | .emptyStr => isTrue ⟨_, .empty⟩
  | (_: α) => isTrue ⟨_, .char⟩
  | re₁ ++ re₂ =>
    match re_not_empty' re₁, re_not_empty' re₂ with
    | isTrue h₁, isTrue h₂ => isTrue <|
      have ⟨_, h₁⟩ := h₁;
      have ⟨_, h₂⟩ := h₂
      ⟨_, .app h₁ h₂⟩
    | isFalse h₁, _ => isFalse fun ⟨_, .app hs₁ _⟩ => h₁ ⟨_, hs₁⟩
    | _, isFalse h₂ => isFalse fun ⟨_, .app _ hs₂⟩ => h₂ ⟨_, hs₂⟩
  | re₁ ∪ re₂ =>
    match re_not_empty' re₁, re_not_empty' re₂ with
    | isTrue h₁, _ => isTrue <| have ⟨s, h₁⟩ := h₁; ⟨s, .unionL h₁⟩
    | _, isTrue h₂ => isTrue <| have ⟨s, h₂⟩ := h₂; ⟨s, .unionR h₂⟩
    | isFalse h₁, isFalse h₂ => isFalse fun
      | ⟨s, .unionL h⟩ => h₁ ⟨s, h⟩
      | ⟨s, .unionR h⟩ => h₂ ⟨s, h⟩
  | _* => isTrue ⟨_, .star0⟩

/- FIXME
theorem re_not_empty_correct
  : (re: RegExp α) → re_not_empty re = (re_not_empty' re).decide
  | ∅ | .emptyStr | (_: α) | _* => rfl
  | re₁ ++ re₂ => by decide
    -- unfold decide; unfold re_not_empty'; simp
    -- have h₁ := re_not_empty_correct re₁
    -- have h₂ := re_not_empty_correct re₂
  | re₁ ∪ re₂ => _
-/
-- (** [] *)

theorem star_app {s₁ s₂: List α} {re: RegExp α}
  : s₁ =~ re* → s₂ =~ re* → s₁ ++ s₂ =~ re*
:= by
  generalize e: re* = r; intros h
  induction h with
  | empty | char | app | unionL | unionR => exact nomatch e
  | star0 => exact id
  | starApp h₁ _ _ ih =>
    exact fun h => List.append_assoc _ _ _ ▸ .starApp h₁ (ih e h)

/-!
### Exercise: 5 stars, advanced (weak_pumping)

One of the first really interesting theorems in the theory of regular 
expressions is the so-called _pumping lemma_, which states, informally, that 
any sufficiently long string `s` matching a regular expression `re` can be 
"pumped" by repeating some middle section of `s` an arbitrary number of times 
to produce a new string also matching `re`. (For the sake of simplicity in this
exercise, we consider a slightly weaker theorem than is usually stated in 
courses on automata theory -- hence the name `weak_pumping`.)

To get started, we need to define "sufficiently long." Since we are working in 
a constructive logic, we actually need to be able to calculate, for each 
regular expression `re`, the minimum length for strings `s` to guarantee 
"pumpability."
-/

namespace Pumping

def pumping_constant: RegExp α → Nat
  | ∅
  | .emptyStr => 1
  | (_: α) => 2
  | re₁ ++ re₂
  | re₁ ∪ re₂ => pumping_constant re₁ + pumping_constant re₂
  | re* => pumping_constant re

/-!
You may find these lemmas about the pumping constant useful when proving the 
pumping lemma below.
-/

theorem pumping_constant_ge_1: (re: RegExp α) → pumping_constant re >= 1
  | ∅
  | .emptyStr => .refl
  | (_: α) => .step .refl
  | re₁ ++ _
  | re₁ ∪ _ => Nat.le_trans (pumping_constant_ge_1 re₁) (Nat.le_add_right _ _)
  | re* => pumping_constant_ge_1 re

theorem pumping_constant_0_false (re: RegExp α): pumping_constant re ≠ 0 :=
  Nat.not_eq_zero_of_lt (pumping_constant_ge_1 re)

/-!
Next, it is useful to define an auxiliary function that repeats a string 
(appends it to itself) some number of times.
-/

def napp: Nat → List α → List α
  | 0, _ => []
  | .succ n, l => l ++ napp n l

/-!
This auxiliary lemma might also be useful in your proof of the pumping lemma.
-/

theorem napp_plus (n m: Nat) (l: List α): napp (n + m) l = napp n l ++ napp m l
:= match n with
  | 0 => m.zero_add.symm ▸ rfl
  | .succ n =>
    List.append_assoc _ _ _ ▸ n.succ_add m ▸ congrArg (l ++ ·) (napp_plus n m l)

theorem napp_star {α m s₁ s₂} {re: RegExp α}
  : s₁ =~ re → s₂ =~ re* → napp m s₁ ++ s₂ =~ re*
  | h₁, h₂ =>
    match m with
    | 0 => h₂
    | .succ _ => List.append_assoc _ _ _ ▸ .starApp h₁ (napp_star h₁ h₂)

/-!
The (weak) pumping lemma itself says that, if `s =~ re` and if the length of 
`s` is at least the pumping constant of `re`, then `s` can be split into three 
substrings `s₁ ++ s₂ ++ s₃` in such a way that `s₂` can be repeated any number 
of times and the result, when combined with `s₁` and `s₃`, will still match 
`re`. Since `s₂` is also guaranteed not to be the empty string, this gives us a 
(constructive!) way to generate strings matching `re` that are as long as we 
like.
-/

-- theorem Nat.add_pigeon {a b c d: Nat} (h: a ≥ c)
--   : a + b ≤ c + d → b ≤ d
--   | h' => Nat.le_of_add_le_add_left <| trans h' (Nat.add_le_add_right h d)

theorem Nat.add_pigeon {a b c d: Nat}: a + b ≤ c + d → a ≤ c ∨ b ≤ d
  | h => if h': a ≤ c then .inl h' else
    have := Nat.le_of_lt (Nat.gt_of_not_le h')
    .inr <| Nat.le_of_add_le_add_left <| trans h (Nat.add_le_add_right this d)

theorem weak_pumping {s: List α} {re: RegExp α} 
  : s =~ re → pumping_constant re ≤ s.length → ∃ s₁ s₂ s₃,
    s = s₁ ++ s₂ ++ s₃ ∧
    s₂ ≠ [] ∧
    ∀ m, s₁ ++ napp m s₂ ++ s₃ =~ re
  | h => h.rec
    (nomatch ·)
    (nomatch ·)
    (fun {t₁ re₁ t₂ re₂} ht₁ ht₂ ih₁ ih₂ hl =>
      (Nat.add_pigeon (List.length_append _ _ ▸ hl)).elim
      (fun hl₁ =>
        have ⟨s₁, s₂, s₃, happ, hnnil, h⟩ := ih₁ hl₁
        ⟨s₁, s₂, s₃ ++ t₂
        , List.append_assoc _ _ _ ▸ congrArg (· ++ t₂) happ, hnnil
        , fun m => List.append_assoc _ _ _ ▸ .app (h m) ht₂⟩
      )
      (fun hl₂ =>
        have ⟨s₁, s₂, s₃, happ, hnnil, h⟩ := ih₂ hl₂
        ⟨t₁ ++ s₁, s₂, s₃
        , by rw [happ]; simp only [List.append_assoc], hnnil
        , fun m =>
          suffices t₁ ++ (s₁ ++ napp m s₂ ++ s₃) = t₁ ++ s₁ ++ napp m s₂ ++ s₃
          from this ▸ .app ht₁ (h m)
          by simp only [List.append_assoc]
        ⟩
      )
    )
    (fun _ ih₁ hl =>
      have ⟨_, _, _, happ, hnnil, h⟩ := ih₁ (trans (Nat.le_add_right _ _) hl)
      ⟨_, _, _, happ, hnnil, fun m => .unionL (h m)⟩
    )
    (fun _ ih₂ hl =>
      have ⟨_, _, _, happ, hnnil, h⟩ := ih₂ (trans (Nat.le_add_left _ _) hl)
      ⟨_, _, _, happ, hnnil, fun m => .unionR (h m)⟩
    )
    (fun hl => nomatch Nat.le_trans (pumping_constant_ge_1 _) hl)
    (fun {s₁ _ _} hs₁ hs₂ _ ih₂ hl =>
      match s₁ with
      | [] => ih₂ hl
      | _::_ => ⟨[], _, _, rfl, (nomatch ·), fun _ => napp_star hs₁ hs₂⟩
    )
-- (** [] *)

/-!
### Exercise: 5 stars, advanced, optional (pumping)

Now here is the usual version of the pumping lemma. In addition to requiring 
that `s₂ ≠ []`, it also requires that 
`s₁.length + s₂.length ≤ pumping_constant re`.
-/

theorem pumping {s: List α} {re: RegExp α}
  : s =~ re → pumping_constant re ≤ s.length → ∃ s₁ s₂ s₃,
    s = s₁ ++ s₂ ++ s₃ ∧
    s₂ ≠ [] ∧
    s₁.length + s₂.length ≤ pumping_constant re ∧
    ∀ m, s₁ ++ napp m s₂ ++ s₃ =~ re
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
        , fun m => List.append_assoc _ _ _ ▸ .app (h m) ht₂⟩
      )
      (fun hl₂ =>
        have ⟨s₁, s₂, s₃, happ, hnnil, hp, h⟩ := ih₂ hl₂
        ⟨t₁ ++ s₁, s₂, s₃
        , by rw [happ]; simp only [List.append_assoc], hnnil
        , sorry
        , fun m =>
          suffices t₁ ++ (s₁ ++ napp m s₂ ++ s₃) = t₁ ++ s₁ ++ napp m s₂ ++ s₃
          from this ▸ .app ht₁ (h m)
          by simp only [List.append_assoc]
        ⟩
      )
    )
    (fun _ ih₁ hl =>
      have ⟨_, _, _, happ, hnnil, hp, h⟩ := ih₁ (trans (Nat.le_add_right _ _) hl)
      ⟨_, _, _, happ, hnnil, trans hp (Nat.le_add_right _ _), fun m => .unionL (h m)⟩
    )
    (fun _ ih₂ hl =>
      have ⟨_, _, _, happ, hnnil, hp, h⟩ := ih₂ (trans (Nat.le_add_left _ _) hl)
      ⟨_, _, _, happ, hnnil, trans hp (Nat.le_add_left _ _), fun m => .unionR (h m)⟩
    )
    (fun hl => nomatch Nat.le_trans (pumping_constant_ge_1 _) hl)
    (fun {s₁ _ _} hs₁ hs₂ _ ih₂ hl =>
      match s₁ with
      | [] => ih₂ hl
      | _::_ => ⟨[], _, _, rfl, (nomatch ·), sorry, fun _ => napp_star hs₁ hs₂⟩
    )
-- (** [] *)

end Pumping

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

#check iff_true
/-- Each provable `Prop` is equivalent to `True`. -/
theorem provable_equiv_true {p: Prop}: p → (p ↔ True)
  | h => ⟨fun _ => trivial, fun _ => h⟩

#check iff_false
/-- Each `Prop` whose negation is provable is equivalent to `False`. -/
theorem not_equiv_false {p: Prop}: ¬p → (p ↔ False)
  | hn => ⟨hn, False.elim⟩

/-- `∅` matches no string. -/
theorem null_matches_none (s: List α): s =~ ∅ ↔ False :=
  -- ⟨(nomatch ·), False.elim⟩
  not_equiv_false (nomatch ·)

/-- `emptyStr` only matches the empty string. -/
theorem empty_matches_eps (s: List α): s =~ .emptyStr ↔ s = [] :=
  ⟨fun | .empty => rfl, (· ▸ .empty)⟩

/-- `emptyStr` matches no non-empty string. -/
theorem empty_nomatch_ne (a: α) (as: List α): a::as =~ .emptyStr ↔ False :=
  not_equiv_false fun h => nomatch (empty_matches_eps (a::as)).mp h

/-- `char a` matches no string that starts with a non-`a` character. -/
theorem char_nomatch_char (a b: α) (bs: List α): b ≠ a → (b::bs =~ a ↔ False)
  | hn => not_equiv_false <| by
    generalize e: b::bs = t
    exact fun .char => hn <| match e with | rfl => rfl

/-- If `char a` matches a non-empty string, then the string's tail is empty. -/
theorem char_eps_suffix (a: α) (s: List α): a::s =~ a ↔ s = [] :=
  .intro
    (by generalize e: a::s = t; exact fun .char => match e with | rfl => rfl)
    (· ▸ .char)

/-- `re₁ ++ re₂` matches string `s` iff `s = s₁ ++ s₂`, where `s₁` matches 
`re₁` and `s₁` matches `re₁`. -/
theorem app_exists (s: List α) (re₁ re₂: RegExp α)
  : s =~ re₁ ++ re₂ ↔ ∃ s₁ s₂, s = s₁ ++ s₂ ∧ s₁ =~ re₁ ∧ s₂ =~ re₂
:= .intro
  fun | .app hs₁ hs₂ => ⟨_, _, rfl, hs₁, hs₂⟩
  fun ⟨_, _, e, hs₁, hs₂⟩ => e ▸ .app hs₁ hs₂

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
  : a::s =~ re₁ ++ re₂ ↔
    [] =~ re₁ ∧ a::s =~ re₂ ∨
    ∃ s₁ s₂, s = s₁ ++ s₂ ∧ a::s₁ =~ re₁ ∧ s₂ =~ re₂
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
    . case inl hs => exact .app hs.1 hs.2
    . case inr h => have ⟨_, _, h, hs₁, hs₂⟩ := h; exact h ▸ .app hs₁ hs₂
-- (** [] *)

/-- `s` matches `Union re₁ re₂` iff `s` matches `re₁` or `s` matches `re₁`. -/
theorem union_disj (s: List α) (re₁ re₂: RegExp α)
  : s =~ re₁ ∪ re₂ ↔ s =~ re₁ ∨ s =~ re₂
:= ⟨fun
    | .unionL hs₁ => .inl hs₁
    | .unionR hs₂ => .inr hs₂
  , (Or.elim · .unionL .unionR)⟩

/-!
### Exercise: 3 stars, standard, optional (star_ne)

`a::s` matches `re*` iff `s = s₁ ++ s₂`, where `a::s₁` matches `re` and `s₁` 
matches `re*`. Like `app_ne`, this observation is critical, so understand it, 
prove it, and keep it in mind.

Hint: you'll need to perform induction. There are quite a few reasonable 
candidates for `Prop`'s to prove by induction. The only one that will work is 
splitting the `iff` into two implications and proving one by induction on the 
evidence for `a::s =~ re*`. The other implication can be proved without 
induction.

In order to prove the right property by induction, you'll need to rephrase 
`a::s =~ re*` to be a `Prop` over general variables, using the `remember` 
tactic.
-/

theorem star_ne (a: α) (s: List α) (re: RegExp α)
  : a::s =~ re* ↔ ∃ s₁ s₂, s = s₁ ++ s₂ ∧ a::s₁ =~ re ∧ s₂ =~ re*
:= by
  constructor
  . case mp =>
    generalize e: a::s = t; intros h
    cases h
    . case star0 => contradiction
    . case starApp s₁ s₂ hs₁ hs₂ =>
      cases s₁
      . case nil => sorry -- ⟨[], s, rfl, _, _⟩
      . case cons _ s₁ => cases e; exact ⟨_, _, rfl, hs₁, hs₂⟩
  . case mpr => exact fun ⟨_, _, e, hs₁, hs₂⟩ => e ▸ .starApp hs₁ hs₂
-- (** [] *)


/-!
The definition of our regex matcher will include two fixpoint functions. The 
first function, given regex `re`, will evaluate to a value that reflects 
whether `re` matches the empty string. The function will satisfy the following 
property:
-/

#check decide
def refl_matches_eps (m: RegExp α → Bool) := ∀ re: RegExp α, [] =~ re ↔ m re
-- def refl_matches_eps (m) (re: RegExp α) := reflect ([] =~ re) (m re)

/-!
### Exercise: 2 stars, standard, optional (match_eps)

Complete the definition of `match_eps` so that it tests if a given regex 
matches the empty string:
-/

def match_eps: RegExp α → Bool
  | ∅ => false
  | .emptyStr => true
  | (a: α) => false
  | re₁ ++ re₂ => match_eps re₁ && match_eps re₂
  | re₁ ∪ re₂ => match_eps re₁ || match_eps re₂
  | _* => true
-- (** [] *)

/-!
### Exercise: 3 stars, standard, optional (match_eps_refl)

Now, prove that `match_eps` indeed tests if a given regex matches the empty 
string. (Hint: You'll want to use the reflection lemmas `ReflectT` and 
`ReflectF`.)
-/

theorem List.nil_of_append_eq_nil
  : {xs ys: List α} → xs ++ ys = [] → xs = [] ∧ ys = []
  | [], _, h => ⟨rfl, h⟩

theorem match_eps_refl: @refl_matches_eps α match_eps :=
  let rec mp {re: RegExp α} {t: List α} (e: t = []): t =~ re → match_eps re
    | .empty
    | .star0
    | .starApp _ _ => rfl
    | .app hs₁ hs₂ =>
      have ⟨e₁, e₂⟩ := List.nil_of_append_eq_nil e
      have h₁ := match_eps_refl.mp e₁ hs₁
      have h₂ := match_eps_refl.mp e₂ hs₂
      Bool.and_eq_true _ _ ▸ And.intro h₁ h₂
    | .unionL hs₁ => match_eps_refl.mp e hs₁ ▸ Bool.true_or _
    | .unionR hs₂ => match_eps_refl.mp e hs₂ ▸ Bool.or_true _
  let rec mpr: {re: RegExp α} → match_eps re → [] =~ re
    | ∅, h => nomatch h
    | .emptyStr, _ => .empty
    | _ ++ _, h =>
      have ⟨h₁, h₂⟩ := Bool.and_eq_true _ _ ▸ h
      .app (mpr h₁) (mpr h₂)
    | _ ∪ _, h => (Bool.or_eq_true _ _ ▸ h).elim (.unionL ∘ mpr) (.unionR ∘ mpr)
    | _*, _ => .star0
  fun _ => ⟨by generalize e: [] = t; exact mp e.symm, mpr⟩
-- (** [] *)

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

def is_der (a: α) (re re': RegExp α) := ∀ s, a::s =~ re ↔ s =~ re'

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

namespace RegExp

instance match_emps (re: RegExp α): Decidable ([] =~ re) :=
  by generalize e: [] = t; exact mp e.symm re
where mp {s: List α} (e: s = []): (re: RegExp α) → Decidable (s =~ re)
  | ∅ => isFalse (nomatch ·)
  | .emptyStr => isTrue (e ▸ .empty)
  | (a: α) => isFalse fun | .char => nomatch e
  | re₁ ++ re₂ =>
    match e.symm with
    | rfl =>
      match mp e re₁, mp e re₂ with
      | isTrue h₁, isTrue h₂ => isTrue (.app h₁ h₂)
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
      | isTrue h₁, _ => isTrue (.unionL h₁)
      | _, isTrue h₂ => isTrue (.unionR h₂)
  | _* => isTrue (e ▸ .star0)

instance (s: List α): Decidable (s =~ ∅) :=
  isFalse (nomatch ·)

instance: (s: List α) → Decidable (s =~ .emptyStr)
  | [] => isTrue .empty
  | x::xs => isFalse <| by generalize e: x::xs = t
    exact fun | .empty => nomatch e

instance [DecidableEq α] (a: α): (s: List α) → Decidable (s =~ a)
  | [b] => if h: a = b then isTrue (h ▸ .char) else
    isFalse <| by generalize e: [b] = t; exact fun | .char =>
      match e with | rfl => h rfl
  | [] => isFalse <| by generalize e: [] = t; exact fun | .char => nomatch e
  | b::c::cs => isFalse <| by generalize e: b::c::cs = t; exact fun | .char =>
    nomatch e

def eqv (re₁ re₂: RegExp α) := ∀ s, s =~ re₁ ↔ s =~ re₂

instance: Setoid (RegExp α) where
  r := eqv
  iseqv := {
    refl := fun _ _ => .rfl
    symm := fun h s => (h s).symm
    trans := fun h₁ h₂ s => (h₁ s).trans (h₂ s)
  }

example (re: RegExp α): ∅ ++ re ≈ ∅ := sorry
example (re: RegExp α): re ++ ∅ ≈ ∅ := sorry
example (re: RegExp α): .emptyStr ++ re ≈ re := sorry
example (re: RegExp α): re ++ .emptyStr ≈ re := sorry
example (re: RegExp α): ∅ ∪ re ≈ re := sorry
example (re: RegExp α): re ∪ ∅ ≈ re := sorry
example (re₁ re₂: RegExp α): re₁ ∪ re₂ ≈ re₂ ∪ re₁ := sorry
example: ∅* ≈ @RegExp.emptySet α := sorry
  -- | s => ⟨
  --   fun
  --     | .starApp hs₁ _ => ((null_matches_none _).mp hs₁).elim
  --     | .star0 => sorry
  --   , MStar1⟩
example: .emptyStr* ≈ @RegExp.emptyStr α := sorry
  -- | s => ⟨
  --   let rec mp {s: List α}: s =~ emptyStr* → s =~ emptyStr
  --     | .starApp hs₁ hs₂ =>
  --       have := mp hs₂
  --       match hs₁, this with | .empty, .empty => .empty
  --     | .star0 => .empty
  --   mp
  --   , MStar1⟩

end RegExp

def derive [DecidableEq α] (a: α): RegExp α → RegExp α
  | ∅
  | .emptyStr => ∅
  | (b: α) => if a = b then .emptyStr else ∅
  | re₁ ++ re₂ => (derive a re₁ ++ re₂) ∪ if [] =~ re₁ then derive a re₂ else ∅
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

/-- `¬ ['c'] =~ ∅` -/
theorem test_der0: ¬ [] =~ derive 'c' ∅ := by decide

/-- `['c'] =~ 'c'` -/
theorem test_der1: [] =~ derive 'c' 'c' := by decide

/-- `¬ ['c'] =~ 'd'` -/
theorem test_der2: ¬ [] =~ derive 'c' 'd' := by decide

/-- `['c'] =~ 'c' ++ .emptyStr` -/
theorem test_der3: [] =~ derive 'c' ('c' ++ .emptyStr) := by decide

/-- `['c'] =~ .emptyStr ++ 'c'` -/
theorem test_der4: [] =~ derive 'c' (.emptyStr ++ 'c') := by decide

/-- `['c'] =~ 'c'*` -/
theorem test_der5: [] =~ derive 'c' 'c'* := by decide

/-- `['c', 'd'] =~ 'c' ++ 'd'` -/
theorem test_der6: [] =~ derive 'd' (derive 'c' ('c' ++ 'd')) := by decide

/-- `¬ ['c', 'd'] =~ 'd' ++ 'c'` -/
theorem test_der7: ¬ [] =~ derive 'd' (derive 'c' ('d' ++ 'c')) := by decide

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
a complicated regex (e.g., `s =~ re₁ ∪ re₂`) to a Boolean combination of 
`Prop`'s over simple regex's (e.g., `s =~ re₁ ∨ s =~ re₂`) using lemmas given 
above that are logical equivalences. You can then reason about these `Prop`'s 
naturally using `intro` and `destruct`.
-/
theorem derive_corr [DecidableEq α]: @derives α derive := sorry
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
  ∀ (s: List α) (re: RegExp α), s =~ re ↔ m s re

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
that `x::s =~ re` given `s =~ derive x re`, and vice versa.
-/

theorem regex_match_correct: @matches_regex α regex_match := sorry
-- (** [] *)
