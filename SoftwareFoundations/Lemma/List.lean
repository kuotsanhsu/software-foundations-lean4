namespace List

universe u
variable {α: Type u}

theorem foldl_append_cons (s: List α)
  : (ss: List (List α)) → (s::ss).foldl .append [] = s ++ ss.foldl .append []
  | [] => (append_nil s).symm
  | s'::ss =>
    calc foldl .append (s ++ s') ss
       = s ++ s' ++ foldl .append [] ss := foldl_append_cons _ _
     _ = s ++ (s' ++ foldl .append [] ss) := append_assoc _ _ _
     _ = s ++ foldl .append s' ss := congrArg (s ++ ·) (foldl_append_cons _ _).symm

theorem mem_of_mem_append {a: α} {ys: List α}
  : {xs: List α} → a ∈ xs ++ ys → a ∈ xs ∨ a ∈ ys
  | [], h => .inr h
  | _::xs, .head _ => .inl (.head xs)
  | x::_, .tail _ h => (mem_of_mem_append h).elim (.inl ∘ .tail x) .inr

#check replicate
/-- Repeats a string (appends it to itself) some number of times. -/
def napp (s: List α): Nat → List α
  | 0 => []
  | .succ n => s ++ napp s n

instance: Pow (List α) Nat where pow := napp

theorem napp_add (s: List α): (m n: Nat) → s^(m + n) = s^m ++ s^n
  | 0, n => n.zero_add.symm ▸ rfl
  | .succ m, n =>
    append_assoc _ _ _ ▸ m.succ_add n ▸ congrArg (s ++ ·) (napp_add s m n)

theorem nil_of_append_eq_nil
  : {xs ys: List α} → xs ++ ys = [] → xs = [] ∧ ys = []
  | [], _, h => ⟨rfl, h⟩

-- instance splitDec {p q: List α → Prop} [dp: DecidablePred p] [dq: DecidablePred q]
--   : (s: List α) → Decidable (∃ sp sq, s = sp ++ sq ∧ p sp ∧ q sq)
--   | [] =>
--     match dp [], dq [] with
--     | isTrue hp, isTrue hq => isTrue ⟨[], [], rfl, hp, hq⟩
--     | isFalse hn, _ => isFalse fun ⟨_, _, e, h, _⟩ =>
--       match (nil_of_append_eq_nil e.symm).1.symm with | rfl => hn h
--     | _, isFalse hn => isFalse fun ⟨_, _, e, _, h⟩ =>
--       match (nil_of_append_eq_nil e.symm).2.symm with | rfl => hn h
--   | a::as =>
--     match dp [a], dq as with
--     | isTrue hp, isTrue hq => isTrue ⟨[a], as, rfl, hp, hq⟩
--     | _, _ => sorry

/-
theorem appendRec {motive: List α → Prop}
  (nil: motive [])
  (app: (s: List α) → (∃ s' s'', s = s' ++ s'' ∧ motive s' ∧ motive s'') → motive s)
  (s: List α): motive s
:=
  s.rec nil fun a as ih => _ --app [a] as ih

noncomputable instance splitDec
  {p q: List α → Prop} [dp: DecidablePred p] [dq: DecidablePred q]
  (s: List α): Decidable (∃ sp sq, s = sp ++ sq ∧ p sp ∧ q sq)
:= by
  induction s using appendRec
  case nil =>
    match dp [], dq [] with
    | isTrue hp, isTrue hq => exact isTrue ⟨[], [], rfl, hp, hq⟩
    | isFalse hn, _ => exact isFalse fun ⟨_, _, e, h, _⟩ =>
      match (nil_of_append_eq_nil e.symm).1.symm with | rfl => hn h
    | _, isFalse hn => exact isFalse fun ⟨_, _, e, _, h⟩ =>
      match (nil_of_append_eq_nil e.symm).2.symm with | rfl => hn h
  case app ih => sorry
-/

end List
