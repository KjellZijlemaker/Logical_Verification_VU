/- Homework 3.2: Program Semantics — Hoare Logic -/

/- Download `x32_library.lean` from the "Logical Verification" homepage and put it in the same
directory as this exercise sheet. -/

import .x32_library

namespace lecture


/- Question 1: Hoare logic for Dijkstra's guarded command language -/

/- Recall the definition of GCL from exercise 3.1: -/

inductive gcl (σ : Type)
| assign : string → (σ → ℕ) → gcl
| assert : (σ → Prop) → gcl
| seq    : gcl → gcl → gcl
| choice : list gcl → gcl
| loop   : gcl → gcl

namespace gcl

variables {p p₀ p₁ p₂ : gcl state} {ps : list (gcl state)}

inductive big_step : (gcl state × state) → state → Prop
| assign {f s n} :
  big_step (assign n f, s) (s.update n (f s))
| assert {c : state → Prop} {s} (hs : c s) :
  big_step (assert c, s) s
| seq {p₁ p₂ s u} (t) (h₁ : big_step (p₁, s) t) (h₂ : big_step (p₂, t) u) :
  big_step (seq p₁ p₂, s) u
| choice {ps : list (gcl state)} {s t} (i : ℕ) (hi : i < list.length ps)
  (h : big_step (list.nth_le ps i hi, s) t) :
  big_step (choice ps, s) t
| loop_base {p s} :
  big_step (loop p, s) s
| loop_step {p s t} (u) (h₁ : big_step (p, s) u) (h₂ : big_step (loop p, u) t) :
  big_step (loop p, s) t

infix ` ⟹ `:110 := big_step

/- The definition of Hoare triples for partial correctness is unsurprising: -/

def partial_hoare (P : state → Prop) (p : gcl state) (Q : state → Prop) : Prop :=
∀s t, P s → (p, s) ⟹ t → Q t

local notation `{* ` P : 1 ` *} ` p : 1 ` {* ` Q : 1 ` *}` := partial_hoare P p Q

namespace partial_hoare

variables {P P' P₁ P₂ P₃ Q Q' : state → Prop} {n : string} {f : state → ℕ}

/- 1.1. Prove the consequence rule. -/

lemma consequence (h : {* P *} p {* Q *}) (hp : ∀s, P' s → P s) (hq : ∀s, Q s → Q' s) :
  {* P' *} p {* Q' *} :=
begin
  intros pq t pqs hpq,
  cases hpq,
  repeat{apply hq,
  apply h pq,
  apply hp},
  repeat{assumption}
end

/- 1.2. Prove the rule for `assign`. -/

lemma assign_intro (P : state → Prop) :
  {* λs:state, P (s.update n (f s)) *} assign n f {* P *} :=
begin
  intros s t ls hls,
  cases hls,
  apply ls
end

/- 1.3. Prove the rule for `assert`. -/

lemma assert_intro :
  {* λs, Q s → P s *} assert Q {* P *} :=
begin
  intros s t sl hsl,
  cases hsl,
  apply sl,
  assumption
end

/- 1.4. Prove the rule for `seq`. -/

lemma seq_intro (h₁ : {* P₁ *} p₁ {* P₂ *}) (h₂ : {* P₂ *} p₂ {* P₃ *}) :
  {* P₁ *} seq p₁ p₂ {* P₃ *} :=
begin
  intros s t ps pst,
  cases pst,
  apply h₂ s, 
  apply h₁ s,
  assumption,
  


end

/- 1.5. Prove the rule for `choice`. -/

lemma choice_intro
  (h : ∀i (hi : i < list.length ps), {* λs, P s *} list.nth_le ps i hi {* Q *}) :
  {* P *} choice ps {* Q *} :=
sorry

/- 1.6. State and prove the rule for `loop`.

    lemma loop_intro ... :
      {* ... *} loop p {* ... *} :=
    ... -/

-- enter your answer here

end partial_hoare

end gcl

/- Background material from the lecture. Do not prove the `sorry`s below. -/

def program.while_inv (I : state → Prop) (c : state → Prop) (p : program) : program :=
program.while c p

open program

variables
  {c : state → Prop} {f : state → ℕ} {n : string}
  {p p₀ p₁ p₂ : program} {s s₀ s₁ s₂ t u : state}
  {P P' P₁ P₂ P₃ Q Q' : state → Prop}

def partial_hoare (P : state → Prop) (p : program) (Q : state → Prop) : Prop :=
∀s t, P s → (p, s) ⟹ t → Q t

notation `{* ` P : 1 ` *} ` p : 1 ` {* ` Q : 1 ` *}` := partial_hoare P p Q

namespace partial_hoare

lemma consequence (h : {* P *} p {* Q *}) (hp : ∀s, P' s → P s) (hq : ∀s, Q s → Q' s) :
  {* P' *} p {* Q' *} :=
sorry

lemma consequence_left (P' : state → Prop) (h : {* P *} p {* Q *}) (hp : ∀s, P' s → P s) :
  {* P' *} p {* Q *} :=
sorry

lemma consequence_right (Q : state → Prop) (h : {* P *} p {* Q *}) (hq : ∀s, Q s → Q' s) :
  {* P *} p {* Q' *} :=
sorry

lemma skip_intro :
  {* P *} skip {* P *} :=
sorry

lemma assign_intro (P : state → Prop) :
  {* λs, P (s.update n (f s)) *} assign n f {* P *} :=
sorry

lemma seq_intro (h₁ : {* P₁ *} p₁ {* P₂ *}) (h₂ : {* P₂ *} p₂ {* P₃ *}) :
  {* P₁ *} seq p₁ p₂ {* P₃ *} :=
sorry

lemma ite_intro (h₁ : {* λs, P s ∧ c s *} p₁ {* Q *}) (h₂ : {* λs, P s ∧ ¬ c s *} p₂ {* Q *}) :
  {* P *} ite c p₁ p₂ {* Q *} :=
sorry

lemma while_intro (P : state → Prop) (h₁ : {* λs, P s ∧ c s *} p {* P *}) :
  {* P *} while c p {* λs, P s ∧ ¬ c s *} :=
sorry

lemma skip_intro' (h : ∀s, P s → Q s):
  {* P *} skip {* Q *} :=
sorry

lemma assign_intro' (h : ∀s, P s → Q (s.update n (f s))):
  {* P *} assign n f {* Q *} :=
sorry

lemma seq_intro' (h₂ : {* P₂ *} p₂ {* P₃ *}) (h₁ : {* P₁ *} p₁ {* P₂ *}) :
  {* P₁ *} p₁ ;; p₂ {* P₃ *} :=
sorry

lemma while_intro_inv (I : state → Prop)
  (h₁ : {* λs, I s ∧ c s *} p {* I *}) (hp : ∀s, P s → I s) (hq : ∀s, ¬ c s → I s → Q s) :
  {* P *} while c p {* Q *} :=
sorry

lemma while_inv_intro {I : state → Prop}
  (h₁ : {* λs, I s ∧ c s *} p {* I *}) (hq : ∀s, ¬ c s → I s → Q s) :
  {* I *} while_inv I c p {* Q *} :=
sorry

lemma while_inv_intro' {I : state → Prop}
  (h₁ : {* λs, I s ∧ c s *} p {* I *}) (hp : ∀s, P s → I s) (hq : ∀s, ¬ c s → I s → Q s) :
  {* P *} while_inv I c p {* Q *} :=
sorry

end partial_hoare

end lecture

namespace tactic.interactive

open lecture.partial_hoare lecture tactic

meta def is_meta {elab : bool} : expr elab → bool
| (expr.mvar _ _ _) := tt
| _                 := ff

meta def vcg : tactic unit := do
  `({* %%P *} %%p {* %%Q *}) ← target
  | skip, -- do nothing if the goal is not a Hoare triple
match p with
| `(program.skip)            := applyc (if is_meta P then ``skip_intro else ``skip_intro')
| `(program.assign _ _)      := applyc (if is_meta P then ``assign_intro else ``assign_intro')
| `(program.ite _ _ _)       := do applyc ``ite_intro; vcg
| `(program.seq _ _)         := do applyc ``seq_intro'; vcg
| `(program.while_inv _ _ _) :=
  do applyc (if is_meta P then ``while_inv_intro else ``while_inv_intro'); vcg
| _                          := fail (to_fmt "cannot analyze " ++ to_fmt p)

end

end tactic.interactive

namespace lecture

open program partial_hoare


/- Question 2: Factorial -/

section FACT

/- The following WHILE program is intended to compute the factorial of `n`, leaving the result in
`r`. -/

def FACT : program :=
assign "r" (λs, 1) ;;
while (λs, s "n" ≠ 0)
( assign "r" (λs, s "r" * s "n") ;;
  assign "n" (λs, s "n" - 1) )

/- 2.1. Define the factorial function. -/

def fact : ℕ → ℕ
:= sorry

/- 2.2. Prove the correctness of `FACT`, using `vcg`. -/

lemma FACT_correct (n : ℕ) :
  {* λs, s "n" = n *} FACT {* λs, s "r" = fact n *} :=
sorry

end FACT

end lecture
