open tactic

-- meta def extract_equals (e : expr) : option (expr × expr) :=
-- match e with
-- | expr.app f x := sorry
-- end


meta def extract_equals : expr → tactic (option (expr × expr))
| (expr.app (expr.app f x) y) :=
  do e ← mk_const `eq,
     trace e,
     trace f,
     if f = e then
       return (some (x, y))
     else
       return none
| _ := none

meta def extract_equals' : expr → option (expr × expr)
| `(%%a = %%b) := some (a, b)
| _ := none


meta def swp : tactic unit :=
do t ← target,
   r ← extract_equals t,
   trace r,
   trace "hello world",
   trace t

meta def swp' : tactic unit :=
do t ← target,
   (a, b) ← extract_equals' t,
   ng ← to_expr ``(%%b = %%a),
   trace (a, b),
   eqs ← to_expr ``(eq.symm),
   apply eqs,
   skip

#check expr
-- set_option pp.all true

lemma foo : 1 + 1 = 3 :=
begin
  symmetry,
  swp',
end