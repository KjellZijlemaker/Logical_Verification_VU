/- Homework 2.4: Functional Programming — Metaprogramming -/

open expr
open tactic
open declaration

example {a b c d e f : Prop} {p : ℕ → Prop} : a → ¬ b ∧ (c ↔ d) :=
begin
intros s,
apply and.intro,
intro l,
end
/- Question 1: A `safe` tactic -/

/- We develop a tactic that applies all safe introduction and elimination rules for the connectives
and quantifiers exhaustively. A rule is said to be _safe_ if it always gives rise to provable
subgoals. In addition, we will require that safe rules do not introduce metavariables (which can
easily be instantiated accidentally with the wrong terms.) We proceed in three steps. -/

/- 1.1. Develop a `safe_intros` tactic that applies the introduction rules for `true', `¬`, `∧`,
`↔`, and `→`/`∀`. (Hint: You can use `tactic.intro` or `tactic.intro1` for some of these.) -/

meta def safe_intros : tactic unit :=
do
tactic.intros,
repeat (applyc `and.intro),
tactic.intro `a2,
repeat (applyc `iff.intro)


example {a b c d e f : Prop} {p : ℕ → Prop} : a → ¬ b ∧ (c ↔ d) :=
begin
  safe_intros,
  /- The proof state should be roughly as follows:

  a b c d e f : Prop,
  p : ℕ → Prop,
  a_1 : a,
  a_2 : b
  ⊢ false

  a b c d e f : Prop,
  p : ℕ → Prop,
  a_1 : a,
  a_2 : c
  ⊢ d

  a b c d e f : Prop,
  p : ℕ → Prop,
  a_1 : a,
  a_2 : d
  ⊢ c -/
  repeat { sorry }
end

/- 1.2. Develop a `safe_destructs` tactic that eliminates `false`, `∧`, `∨`, `↔`, and `∃`. -/

meta def safe_destructs : tactic unit := do
tactic.intros,
applyc (`false.elim),
applyc (`and.elim)


example {a b c d e f : Prop} {p : ℕ → Prop}
  (hneg: ¬ a) (hand : a ∧ b ∧ c) (hor : c ∨ d) (himp : b → e) (hiff : e ↔ f) (hex : ∃x, p x) :
  false :=
begin
  safe_destructs,
  /- The proof state should be roughly as follows:

  2 goals
  a b c d e f : Prop,
  p : ℕ → Prop,
  hneg : ¬a,
  himp : b → e,
  hand_left : a,
  hor : c,
  hiff_mp : e → f,
  hiff_mpr : f → e,
  hex_w : ℕ,
  hex_h : p hex_w,
  hand_right_left : b,
  hand_right_right : c
  ⊢ false

  a b c d e f : Prop,
  p : ℕ → Prop,
  hneg : ¬a,
  himp : b → e,
  hand_left : a,
  hor : d,
  hiff_mp : e → f,
  hiff_mpr : f → e,
  hex_w : ℕ,
  hex_h : p hex_w,
  hand_right_left : b,
  hand_right_right : c
  ⊢ false -/
  repeat { sorry }
end

/- 1.3. Implement a `safe` tactic that first performs introduction, then elimination, and finally
proves all the subgoals that can be discharged directly by `assumption`.

Hint: The `try` tactic combinator might come in handy. -/

meta def safe : tactic unit :=
sorry

example {a b c d e f : Prop} {p : ℕ → Prop}
(hneg: ¬ a) (hand : a ∧ b ∧ c) (hor : c ∨ d) (himp : b → e) (hiff : e ↔ f) (hex : ∃x, p x) :
  a → ¬ b ∧ (c ↔ d) :=
begin
  safe,
  /- The proof state should be roughly as follows:

  3 goals
  a b c d e f : Prop,
  p : ℕ → Prop,
  hneg : ¬a,
  himp : b → e,
  a_1 : a,
  a_2 : b,
  hand_left : a,
  hor : c,
  hiff_mp : e → f,
  hiff_mpr : f → e,
  hex_w : ℕ,
  hex_h : p hex_w,
  hand_right_left : b,
  hand_right_right : c
  ⊢ false

  a b c d e f : Prop,
  p : ℕ → Prop,
  hneg : ¬a,
  himp : b → e,
  a_1 : a,
  a_2 : b,
  hand_left : a,
  hor : d,
  hiff_mp : e → f,
  hiff_mpr : f → e,
  hex_w : ℕ,
  hex_h : p hex_w,
  hand_right_left : b,
  hand_right_right : c
  ⊢ false

  a b c d e f : Prop,
  p : ℕ → Prop,
  hneg : ¬a,
  himp : b → e,
  a_1 : a,
  a_2 : c,
  hand_left : a,
  hor : c,
  hiff_mp : e → f,
  hiff_mpr : f → e,
  hex_w : ℕ,
  hex_h : p hex_w,
  hand_right_left : b,
  hand_right_right : c
  ⊢ d -/
  repeat { sorry }
end


/- Question 2: A `solve_direct` advisor -/

/- It often happens that a user states a new lemma, proves it, and later realizes that the lemma
already exists in the library. To help prevent this, we want to implement a `solve_direct` tactic,
which goes through all lemmas in the database and checks whether one of them can be used to fully
solve the statement. We implement it in steps. -/

/- 2.1. Develop a function that returns `tt` if a `declaration` is a theorem (`declaration.thm`) or
an axiom (`declaration.ax`) and `ff` otherwise. -/

meta def is_theorem : declaration → bool
:= sorry

/- 2.2. Develop a function that returns the list of all theorem names (theorem in the sense of
`is_theorem`).

Here `get_env` and `environment.fold` are very helpful. See also Question 3 of the exercise. -/

meta def get_all_theorems : tactic (list name) :=
sorry

/- 2.3. Develop a tactic that (fully) solves the goal using a theorem `n`.

Hints:

* `mk_const n` can be used to produce an `expr` (representing the proof) from a name `n` (the
theorem name).

* `apply` applies an `expr` to the current goal. For speed reasons one might want to add the
c onfiguration `apply c { md := transparency.reducible, unify := ff }`, where `c : expr` is the
current theorem, and the parameters in `{ ... }` tell `apply` to apply less computational unfolding.

* `all_goals` in combination with `assumption` can be used to ensure that the hypothesis from the
local context are used to fill in all remaining subgoals.

* `done` can be used to check that no subgoal is left. -/

meta def solve (n : name) : tactic unit :=
sorry

/- 2.4. Implement `solve_direct`.

Now `solve_direct` should go through `get_all_theorems` and succeed with the first theorem solving
the current goal.

You can use `list.mfirst` to apply a tactic to each element of a list until one application
succeeds. Use `trace` to output the successful theorem to the user. -/

meta def solve_direct : tactic unit :=
sorry

/- 2.5. Develop a version of `solve_direct` that also looks for equalities stated in symmetric form
(e.g., if the goal is `l = r` but the theorem is `r = l`). -/

#check eq.symm

meta def solve_direct_symm : tactic unit :=
sorry

example {n : ℕ} : n + 0 = n := by solve_direct_symm
example {n : ℕ} : n = n + 0 := by solve_direct_symm


/- Question 3 **optional**: An `auto` tactic -/

/- 3.1. Develop an Isabelle-style `auto` tactic.

This tactic would apply all safe introduction and elimination rules. In addition, it would try
unsafe rules (such as `or.intro_left` and `false.elim`) but backtrack at some point
(or try several possibilities in parallel). Iterative deepening may be a valid approach, or
best-first search, or breadth-first search. The tactic should also attempt to apply assumptions
whose conclusion matches the goal, but backtrack if necessary.

See also "Automatic Proof and Disproof in Isabelle/HOL"
(https://www.cs.vu.nl/~jbe248/frocos2011-dis-proof.pdf) by Blanchette, Bulwahn, and Nipkow, and the
references they give. -/

/- 3.2. Test your tactic on some benchmarks.

You can try your tactic on logical puzzles of the kinds we proved in exercise 1.3 and howework 1.3.
Please include these below. -/
