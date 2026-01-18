/-===========================================-/
/-===========================================-/
/-===                                     ===-/
/-===   Ordinary functional programming   ===-/
/-===                                     ===-/
/-===========================================-/
/-===========================================-/

/-=========================-/
/- Variables and functions -/
/-=========================-/

/-
  Sometimes it's useful to ask Lean for the type of an expression. We can use
  the `#check` command for that. For example, the type of the expression below
  is `Nat`, which stands for "natural number". Natural numbers are unsigned
  integers, and they're the most common type of number in Lean.

  To use these commands interactively, be sure you're using the Lean plugin for
  Visual Studio Code.
-/

#check 3 + 4 -- `Nat`

/- If we want Lean to actually evaluate an expression, we can use `#eval`. -/

#eval 3 + 4 -- `7`
