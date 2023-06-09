namespace List
universe u
variable {α: Type u}

/-- A palindrome is a sequence of symbols that reads the same backwards as 
forwards: https://en.wikipedia.org/wiki/Palindrome -/
def Palindrome (α: Type u) := { s: List α // s = s.reverse }

theorem dropLast_append_last
  : (s: List α) → (nonempty: s ≠ []) → s.dropLast ++ [s.getLast nonempty] = s
  | [_], _ => rfl
  | a::b::s, _ => congrArg (a::·) (dropLast_append_last (b::s) _)

theorem revRec {motive: List α → Prop}
    (nil: motive [])
    (revCons: (s: List α) → (b: α) → motive s → motive (s ++ [b]))
  : (s: List α) → motive s
  | [] => nil
  | a::s =>
    have := revRec nil revCons (a::s).dropLast
    have := revCons _ ((a::s).getLast (nomatch ·)) this
    dropLast_append_last (a::s) _ ▸ this
termination_by _ s => s.length

theorem doubleRec {motive: List α → Prop}
    (nil: motive [])
    (single: (a: α) → motive [a])
    (doubleCons: (a: α) → (s: List α) → (b: α) → motive s → motive (a::s ++ [b]))
  : (s: List α) → motive s
  | [] => nil
  | [a] => single a
  | a::b::s =>
    have := doubleRec nil single doubleCons (b::s).dropLast
    have := doubleCons a _ ((b::s).getLast (nomatch ·)) this
    dropLast_append_last (b::s) _ ▸ this
termination_by _ s => s.length

inductive palindromic: List α → Prop
  | nil: palindromic []
  | single (a: α): palindromic [a]
  | sandwich (a: α) {s: List α}: palindromic s → palindromic (a::s ++ [a])

theorem Palindrome.isPalindromic: (s: Palindrome α) → palindromic s.val
  | ⟨v, p⟩ => aux v p.symm
where aux (s: List α) (h: s.reverse = s): palindromic s := by
        induction s using doubleRec
        case nil => exact .nil
        case single a => exact .single a
        case doubleCons a s b ih =>
          have: a = b := by simp_all
          subst this
          have: s.reverse = s := by simp_all
          exact .sandwich a (ih this)



-- theorem palindrome_reverse {s: List α}: Palindrome s → Palindrome s.reverse
--   | .nil => .nil
--   | .single => .single
--   | .sandwich h => by simp; exact .sandwich (palindrome_reverse h)
-- termination_by _ => s.length

theorem reverse_eq_of_palindrome {s: List α}: palindromic s → s = s.reverse
  | .nil | .single _ => rfl
  | .sandwich _ h => by simp; exact reverse_eq_of_palindrome h
termination_by _ => s.length

example {s: List α}: palindromic s → palindromic s.reverse
 | h => reverse_eq_of_palindrome h ▸ h

end List

#check Iff.of_eq
#check proofIrrel
#check propext
#check Eq.propIntro
#check instDecidableEqProp

#check decPropToBool
#check toBoolUsing
#check Bool.decEq
