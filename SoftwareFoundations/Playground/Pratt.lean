/-
- https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
- https://matklad.github.io/2020/04/15/from-pratt-to-dijkstra.html
- https://www.oilshell.org/blog/2016/11/05.html
- https://leanprover.github.io/lean4/doc/monads/transformers.lean.html
-/

inductive Token
  | literal (value: Int)
  -- | identifier (name: String)
  | «+» | «-» | «*» | «/» | «++» | «--»
  | «(» | «)» | «[» | «]» | «?» | «:»
  deriving DecidableEq

instance: Coe Int Token where coe := .literal
instance {n: Nat}: OfNat Token n where ofNat := n
-- instance: Coe String Token where coe := .identifier

inductive Expr
  | const (value: Int)
  | pos (e: Expr)
  | neg (e: Expr)
  | pre_inc (e: Expr)
  | pre_dec (e: Expr)
  | post_inc (e: Expr)
  | post_dec (e: Expr)
  | add (left right: Expr)
  | sub (left right: Expr)
  | mul (left right: Expr)
  | div (left right: Expr)
  | get (collection key: Expr)
  | ite (condition true false: Expr)

/-!
Monadic list with next and peek.
-/

abbrev TokenStream := List Token

def TokenStream.next: EStateM String TokenStream Token := do
  match ← get with
  | [] => throw "Expects a token but got nothing"
  | token::tokens => set tokens; return token

def TokenStream.peek: EStateM String TokenStream (Option Token) :=
  return match ← get with
  | [] => none
  | token::_ => token


def infix_binding_power (token: Token): EStateM String TokenStream (Option (Nat × Nat)) :=
  open Token in
  return match token with
  | «+» | «-» => (5, 6)
  | «*» | «/» => (7, 8)
  | _ => none


open Token in
def expr_bp (min_bp: Nat): EStateM String TokenStream Expr := do
  let lhs: Expr ←
    match ← TokenStream.next with
    | literal value => return .const value
    | «(» =>
      let lhs ← expr_bp 0
      -- assert! (← TokenStream.next) = «)»
      if (← TokenStream.next) ≠ «)» then
        throw "Expects `)`"
      return lhs
    | _ => throw "Expects a token but got nothing"
  
  -- FIXME: Should loop infinitely
  -- let bp :=
  match ← TokenStream.peek with
  | none => return lhs
  | some op =>
    -- return lhs
    -- (1, 2) --let rhs ← expr_bp 1
    let bps: Option (Nat × Nat) ← infix_binding_power op
    if let some ⟨l_bp, r_bp⟩ := bps then
      let op ← TokenStream.next
      let rhs ← expr_bp r_bp
      return rhs

-- def expr (tokens: List Token): Except String Expr :=
--   expr_bp.run tokens

def expr: EStateM String TokenStream Expr :=
  expr_bp 0

#check StateT
#check modify
/-


#check IO
#check OptionT

namespace MonadPlayground

instance: Monad Option where
  pure := some
  bind opt next := match opt with | none => none | some x => next x

def optionFunc1: String → Option Nat
  | "" => none
  | str => some str.length

def optionFunc2 (i: Nat): Option Float :=
  if i % 2 == 0 then none else some (i.toFloat * 3.14)

def optionFunc3 (f: Float): Option (List Nat) :=
  if f > 15 then none else some [f.floor.toUInt32.toNat, f.ceil.toUInt32.toNat]

def runOptionFuncs (input: String): Option (List Nat) :=
  match optionFunc1 input with
  | none => none
  | some i =>
    match optionFunc2 i with
    | none => none
    | some f => optionFunc3 f

#eval runOptionFuncs "big"

def runOptionFuncsBind (input: String): Option (List Nat) :=
  optionFunc1 input >>= optionFunc2 >>= optionFunc3

#eval runOptionFuncsBind "big"

def runOptionFuncsDo (input: String): Option (List Nat) := do
  let i ← optionFunc1 input
  let f ← optionFunc2 i
  optionFunc3 f

#eval runOptionFuncsDo "big"

def runOptionFuncsDo2 (input: String): Option (List Nat) := do
  optionFunc3 (← optionFunc2 (← optionFunc1 input))

namespace Reader'

structure Environment where
  path: String
  home: String
  user: String
  deriving Repr

def getEnvDefault1 (name: String): IO String :=
  IO.getEnv name >>= fun x => pure (x.getD "")

def getEnvDefault2 (name: String): IO String := do
  pure <| match ← IO.getEnv name with
    | none => ""
    | some s => s

def getEnvDefault3 (name: String): IO String :=
  return match ← IO.getEnv name with
    | none => ""
    | some s => s

def getEnvDefault (name: String): IO String :=
  return (← IO.getEnv name).getD ""

def loadEnv: IO Environment :=
  return {
    path := ← getEnvDefault "PATH"
    home := ← getEnvDefault "HOME"
    user := ← getEnvDefault "USER"
  }

def func1 (e: Environment): Nat :=
  e.path.length + e.home.length + e.user.length

def func1' (e: Environment): String :=
  "Result: " ++ toString (func1 e)

def main1: IO Unit := do
  IO.println (func1' (← loadEnv))



def func2: ReaderM Environment Nat :=
  return let e := ← read; e.path.length + e.home.length + e.user.length

def func2': ReaderM Environment String :=
  return "Result: " ++ toString (← func2)

def main2: IO Unit := do
  IO.println (func2'.run (← loadEnv))

def main2': IO Unit := do
  IO.println (func2' (← loadEnv))

end Reader'

end MonadPlayground

#check ReaderT.read
#check StateT.get
#check StateM
#check IO.getStdin
#check IO.FS.Handle.getLine


-/
