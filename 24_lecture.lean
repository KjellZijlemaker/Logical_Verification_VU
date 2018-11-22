/- Lecture 2.4: Functional Programming — Metaprogramming -/

/- Tactics -/

example : true :=
  by tactic.triv

example : true := by do
  tactic.trace "Hello, Metacosmos!",
  tactic.triv

meta def hello_world : tactic unit := do
  tactic.trace "Hello, Metacosmos!",
  tactic.triv

example : true := by hello_world

run_cmd hello_world

open tactic

example (α : Type) (a : α) : true := by do
  trace "local context:",
    local_context >>= trace,
  trace "goals:",
    get_goals >>= trace,
  trace "target:",
    target >>= trace,
  triv

meta def exact_list : list expr → tactic unit
| []        := fail "no matching expression found"
| (e :: es) :=
  (do
    trace "trying ",
    trace e,
    exact e)
  <|> exact_list es

meta def find_assumption : tactic unit := do
  es ← local_context,
  exact_list es

example {p : Prop} {α : Type} (a : α) (h : p) : p := by do
  find_assumption

example {p : Prop} (h : p) : p := by do
  p_proof ← get_local `h,
  trace "p_proof:",
    trace p_proof,
    trace p_proof.to_raw_fmt,
  trace "type of p_proof:",
    infer_type p_proof >>= trace,
  trace "type of type of p_proof:",
    infer_type p_proof >>= infer_type >>= trace,
  apply p_proof


/- Names and expressions -/

#print expr

#check expr tt  -- elaborated expressions
#check expr ff  -- unelaborated expressions (pre-expressions)

#print name

#check (expr.const `ℕ [] : expr)

#check expr.sort level.zero  -- Sort 0, i.e. Prop
#check expr.sort (level.succ level.zero)  -- Sort 1, i.e. Type 0 (Type)

#check expr.app
#check expr.var 0  -- bound variable of De Bruijn index 0
#check (expr.local_const `uniq_name `pp_name binder_info.default `(ℕ) : expr)
#check (expr.mvar `uniq_name `pp_name `(ℕ) : expr)
#check (expr.pi `pp_name binder_info.default `(ℕ) (expr.sort level.zero) : expr)
#check (expr.lam `pp_name binder_info.default `(ℕ) (expr.var 0) : expr)
#check expr.elet
#check expr.macro


/- Name literals -/

run_cmd trace `name.a
run_cmd trace ``true
run_cmd trace ``name.a -- not found


/- Expression literals -/

-- one backtick: fully elaborated expressions (using reflection)

run_cmd do
  let e : expr := `(list.map (λn : ℕ, n + 1) [1, 2, 3]),
  trace e

run_cmd do
  let e : expr := `(list.map _ [1, 2, 3]),  -- error: holes not allowed
  skip

-- two backticks: checked pre-expressions

run_cmd do
  let e₀ : pexpr := ``(list.map (λn, n + 1) [1, 2, 3]),
  let e₁ : pexpr := ``(list.map _ [1, 2, 3]),
  trace e₀,
  trace e₁

-- three backticks: pre-expressions without name checking

run_cmd do
  let e := ```(a),
  trace e


/- Antiquotations -/

run_cmd do
  let x : expr := `(2 : ℕ),
  let e : expr := `(%%x + 1),
  trace e

run_cmd do
  let x : expr := `(@id ℕ),
  let e := ``(list.map %%x),
  trace e

run_cmd do
  let x : expr := `(@id ℕ),
  let e := ```(a _ %%x),
  trace e


/- Pattern matching -/

example : 1 + 2 = 3 := by do
  `(%%a + %%b = %%r) ← target,
  trace a, trace b, trace r,
  `(@eq %%α %%l' %%r') ← target,
  trace α, trace l', trace r',
  exact `(refl _ : 3 = 3)


/- A simple tactic: `destruct_and` -/

example {a b c d : Prop} (h : a ∧ (b ∧ c) ∧ d) : a := and.left h
example {a b c d : Prop} (h : a ∧ (b ∧ c) ∧ d) : b := and.left (and.left (and.right h))
example {a b c d : Prop} (h : a ∧ (b ∧ c) ∧ d) : b ∧ c := and.left (and.right h)

-- `destruct_and_core t h` uses the conjunction `h : t` to prove the current goal
meta def destruct_and_core : expr → expr → tactic unit
| `(%%a ∧ %%b) h :=
    exact h
    <|> (to_expr ``(and.left %%h) >>= destruct_and_core a)
    <|> (to_expr ``(and.right %%h) >>= destruct_and_core b)
| _            h := exact h

meta def destruct_and (h : name) : tactic unit := do
  h ← get_local h,
  t ← infer_type h,
  destruct_and_core t h

example {a b c d : Prop} (h : a ∧ (b ∧ c) ∧ d) : a := by destruct_and `h
example {a b c d : Prop} (h : a ∧ (b ∧ c) ∧ d) : b := by destruct_and `h
example {a b c d : Prop} (h : a ∧ (b ∧ c) ∧ d) : b ∧ c := by destruct_and `h
example {a b c d : Prop} (h : a ∧ (b ∧ c) ∧ d) : b ∧ d := by destruct_and `h  -- fails

#check exact
#check interactive.exact
#check lean.parser

open interactive.types

meta def tactic.interactive.destruct_and (h : interactive.parse ident_) : tactic unit :=
destruct_and h

example {a b c d : Prop} (h : a ∧ (b ∧ c) ∧ d) : a :=
by destruct_and h
