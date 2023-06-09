/--
```
Dyck ::=
  | "(" Dyck ")"
  | "{" Dyck "}"
  | end
```
-/
inductive Dyck
  | parentheses (enclosure: Dyck)
  | braces (enclosure: Dyck)
  | end

declare_syntax_cat Dyck
syntax "`[Dyck| " Dyck "]" : term
syntax "(" Dyck ")" : Dyck
syntax "{" Dyck "}" : Dyck
syntax "end" : Dyck

macro_rules
  | `(`[Dyck| end]) => `(Dyck.end)
  | `(`[Dyck| ($e)]) => `(Dyck.parentheses `[Dyck| $e])
  | `(`[Dyck| {$e}]) => `(Dyck.braces `[Dyck| $e])

#check `[Dyck| end]
#check `[Dyck| (end)]
#check `[Dyck| {(end)}]
