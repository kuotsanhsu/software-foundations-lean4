import FormalLanguage.Def
import SoftwareFoundations.Lemma

namespace RegExp
universe u
variable {α: Type u} [DecidableEq α]

section
variable {a b: α} {s: List α} {r r₁ r₂: RegExp α}

theorem accept_nothing: ¬ s =~ ∅ := (nomatch ·)

theorem accept_empty: s =~ ε → s = []
  | empty => rfl

theorem accept_single: s =~ a → s = [a]
  | single => rfl

example: a::s =~ b → a = b
  | h => match accept_single h with | rfl => rfl

example: a::s =~ b → s = []
  | h => match accept_single h with | rfl => rfl

example: s =~ ∅* → s = []
  | starEmpty => rfl

example: s =~ r → s =~ r*
  | h => s.append_nil ▸ (starAppend h starEmpty)

theorem app_exists: s =~ r₁ ++ r₂ → ∃ s₁ s₂, s = s₁ ++ s₂ ∧ s₁ =~ r₁ ∧ s₂ =~ r₂
  | append h₁ h₂ => ⟨_, _, rfl, h₁, h₂⟩

theorem union_disj: s =~ r₁ ∪ r₂ → s =~ r₁ ∨ s =~ r₂
  | unionL h => .inl h
  | unionR h => .inr h

theorem cons_accept_append
  : a::s =~ r₁ ++ r₂
  → (∃ s₁ s₂, s = s₁ ++ s₂ ∧ a::s₁ =~ r₁ ∧ s₂ =~ r₂) ∨
    ([] =~ r₁ ∧ a::s =~ r₂)
:= by
  generalize et: a::s = t
  intro
  | append (s₁ := []) h₁ h₂ => exact .inr ⟨h₁, h₂⟩
  | append (s₁ := b::s₁) h₁ h₂ =>
    cases et; exact .inl ⟨_, _, rfl, h₁, h₂⟩

instance match_empty: (r: RegExp α) → Decidable ([] =~ r)
  | .nothing => isFalse accept_nothing
  | ε => isTrue empty
  | (a: α) => isFalse (nomatch accept_single ·)
  | r₁ ++ r₂ =>
    match match_empty r₁, match_empty r₂ with
    | isTrue h₁, isTrue h₂ => isTrue (append h₁ h₂)
    | isFalse hn, _ => isFalse fun h =>
      have ⟨_, _, e, h, _⟩ := app_exists h
      hn <| (List.nil_of_append_eq_nil e.symm).1 ▸ h
    | _, isFalse hn => isFalse fun h =>
      have ⟨_, _, e, _, h⟩ := app_exists h
      hn <| (List.nil_of_append_eq_nil e.symm).2 ▸ h
  | r₁ ∪ r₂ =>
    match match_empty r₁, match_empty r₂ with
    | isFalse hn₁, isFalse hn₂ => isFalse fun h => (union_disj h).elim hn₁ hn₂
    | isTrue h, _ => isTrue (unionL h)
    | _, isTrue h => isTrue (unionR h)
  | _* => isTrue starEmpty

theorem starRec {motive: ∀ {s}, s =~ r* → Prop}
  (base: motive starEmpty)
  (ind: ∀ {s₁ s₂}, (h₁: s₁ =~ r) → (h₂: s₂ =~ r*)
    → motive h₂ → motive (starAppend h₁ h₂))
  {s} (h: s =~ r*): motive h
:= by
  generalize er: r* = r; rw [er] at h
  induction h
  case empty | single | append | unionL | unionR => exact nomatch er
  case starEmpty => exact base
  case starAppend s₁ s₂ _ h₁ h₂ _ ih =>
    cases er; cases s₁
    . case nil => exact ih h rfl
    . case cons => exact ind h₁ h₂ (ih h₂ rfl)

theorem cons_accept_star
  : a::s =~ r* → ∃ s₁ s₂, s = s₁ ++ s₂ ∧ a::s₁ =~ r ∧ s₂ =~ r*
:= by
  generalize et: a::s = t
  intros h
  induction h using starRec
  case base => exact nomatch et
  case ind s₁ s₂ h₁ h₂ ih =>
    cases s₁
    . case nil => exact ih et
    . case cons => cases et; exact ⟨_, _, rfl, h₁, h₂⟩

end

class Der (der: α → RegExp α → RegExp α) where
  law (a s r): a::s =~ r ↔ s =~ der a r

/--
- [Brzozowski derivative](https://en.wikipedia.org/wiki/Brzozowski_derivative)
- [Myhill–Nerode theorem](https://en.wikipedia.org/wiki/Myhill%E2%80%93Nerode_theorem)
-/
def derive (a: α): RegExp α → RegExp α
  | .nothing | ε => ∅
  | (b: α) => if a = b then ε else ∅
  | r₁ ++ r₂ =>
    if [] =~ r₁ then (derive a r₁ ++ r₂) ∪ derive a r₂ else derive a r₁ ++ r₂
  | r₁ ∪ r₂ => derive a r₁ ∪ derive a r₂
  | r* => derive a r ++ r*

instance derives: @Der α derive where
  law _ _ _ :=
    let rec mp {a} {s: List α}: {r: RegExp α} → a::s =~ r → s =~ derive a r
      | .nothing, h => absurd h accept_nothing
      | ε, h => nomatch accept_empty h
      | (b: α), h =>
        match (accept_single h).symm with | rfl => trans empty (if_pos rfl).symm
      | r ++ _, h =>
        (cons_accept_append h).elim
        fun | ⟨_, _, h, h₁, h₂⟩ =>
              have := h.symm ▸ append (mp h₁) h₂
              if e: [] =~ r
              then trans (unionL this) (if_pos e).symm
              else trans this (if_neg e).symm
        fun ⟨e, h₂⟩ => trans (unionR (mp h₂)) (if_pos e).symm
      | _ ∪ _, h => (union_disj h).elim (unionL ∘ mp) (unionR ∘ mp)
      | _*, h =>
        have ⟨_, _, h, h₁, h₂⟩ := cons_accept_star h; h ▸ append (mp h₁) h₂
    let rec mpr {a} {s: List α}: {r: RegExp α} → s =~ derive a r → a::s =~ r
      | (b: α), h => if e: a = b
        then match trans h (if_pos e) with | empty => e ▸ single
        else nomatch trans h (if_neg e)
      | r ++ _, h => if e: [] =~ r
        then
          match trans h (if_pos e) with
          | unionL (append h₁ h₂) => append (mpr h₁) h₂
          | unionR h₂ => append e (mpr h₂)
        else
          match trans h (if_neg e) with
          | append h₁ h₂ => append (mpr h₁) h₂
      | _ ∪ _, unionL h => unionL (mpr h)
      | _ ∪ _, unionR h => unionR (mpr h)
      | _*, append h₁ h₂ => starAppend (mpr  h₁) h₂
    ⟨mp, mpr⟩

instance decAccept (s: List α) (r: RegExp α): Decidable (s =~ r) :=
  match s with
  | [] => match_empty r
  | a::s =>
    match decAccept s (derive a r) with
    | isTrue h => isTrue (derives.mpr h)
    | isFalse hn => isFalse (hn ∘ derives.mp)

end RegExp
