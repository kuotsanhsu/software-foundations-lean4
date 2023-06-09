namespace Nat
-- theorem add_pigeon {a b c d: Nat} (h: a ≥ c)
--   : a + b ≤ c + d → b ≤ d
--   | h' => Nat.le_of_add_le_add_left <| trans h' (Nat.add_le_add_right h d)

theorem add_pigeon {a b c d: Nat}: a + b ≤ c + d → a ≤ c ∨ b ≤ d
  | h => if h': a ≤ c then .inl h' else
    have := Nat.le_of_lt (Nat.gt_of_not_le h')
    .inr <| Nat.le_of_add_le_add_left <| trans h (Nat.add_le_add_right this d)

end Nat