inductive Term
  | true
  | false
  | var (identifier: String)
  | not (p: Term)
  | and (p q: Term)
  | or (p q: Term)
  | imply (p q: Term)

#check 1 ∧ 2
