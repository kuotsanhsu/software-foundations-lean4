/-!
## Fold

An even more powerful higher-order function is called `fold`. This function is 
the inspiration for the `reduce` operation that lies at the heart of Google's 
map/reduce distributed programming framework.
-/

def fold.{u} {α β: Type u} (f: α → β → β) (l: List α) (b : β): β :=
  match l with
  | [] => b
  | x::xs => f x (fold f xs b)
