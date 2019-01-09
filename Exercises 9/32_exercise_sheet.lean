/- Exercise 3.2: Program Semantics — Hoare Logic -/

/- Download `x32_library.lean` from the "Logical Verification" homepage and put it in the same
directory as this exercise sheet. -/

import .x32_library

namespace lecture


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
begin
  intro s,
  intro hst,
  intro p,
  intro ps,
  cases ps,
  apply hq,
  apply h s,
  apply hp,
  assumption,
  assumption,
  cases ps,
  apply hq,
  apply h s,
  apply hp,
  assumption,
  generalize eq : (assign ps_n ps_f, s) = ps,

end

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


/- Question 1: Program verification -/

section GAUSS

/- The following WHILE program is intended to compute the Gaussian sum up to `n`, leaving the result
in `r`. -/

def GAUSS : program :=
assign "r" (λs, 0) ;;
while (λs, s "n" ≠ 0)
( assign "r" (λs, s "r" + s "n") ;;
  assign "n" (λs, s "n" - 1) )
big_step.ite_false
/- The summation function: -/

def sum_upto : ℕ → ℕ
| 0       := 0
| (n + 1) := n + 1 + sum_upto n

/- 1.1. Prove the correctness of `GAUSS`, using `vcg`. The main challenge is to figure out which
invariant to use for the while loop. The invariant should capture both the work that has been done
already (the intermediate result) and the work that remains to be done. -/

lemma GAUSS_correct (n : ℕ) :
  {* λs, s "n" = n *} GAUSS {* λs, s "r" = sum_upto n *} :=
sorry

end GAUSS

section MUL

/- The following WHILE program is intended to compute the product of `n` and `m`, leaving the
result in `r`. -/

def MUL : program :=
assign "r" (λs, 0) ;;
while (λs, s "n" ≠ 0)
( assign "r" (λs, s "r" + s "m") ;;
  assign "n" (λs, s "n" - 1) )

/- 1.2 Prove the correctness of `MUL`, using `vcg`.

Hint: If a variable `x` does not change in a program, it might be useful to record this in the
invariant, by adding a conjunct `s "x" = x`. -/

lemma MUL_correct (n m : ℕ) :
  {* λs, s "n" = n ∧ s "m" = m *} MUL {* λs, s "r" = n * m *} :=
sorry

end MUL


/- Question 2: Hoare triples for total correctness -/

def total_hoare (P : state → Prop) (p : program) (Q : state → Prop) : Prop :=
∀s, P s → ∃t, (p, s) ⟹ t ∧ Q t

notation `[* ` P : 1 ` *] ` p : 1 ` [* ` Q : 1 ` *]` := total_hoare P p Q

namespace total_hoare
variables {P P' P₁ P₂ P₃ Q Q' : state → Prop} {n : string}
variables {p p₀ p₁ p₂ : program}
variables {c : state → Prop} {f : state → ℕ}
  {s s₀ s₁ s₂ t u : state}

/- 2.1. Prove the consequence rule. -/

lemma consequence (h : [* P *] p [* Q *]) (hp : ∀s, P' s → P s) (hq : ∀s, Q s → Q' s) :
  [* P' *] p [* Q' *] :=
sorry

/- 2.2. Prove the rule for `skip`. -/

lemma skip_intro :
  [* P *] skip [* P *] :=
sorry

/- 2.3. Prove the rule for `assign`. -/

lemma assign_intro (P : state → Prop) :
  [* λs, P (s.update n (f s)) *] assign n f [* P *] :=
sorry

/- 2.4. Prove the rule for `seq`. -/

lemma seq_intro (h₁ : [* P₁ *] p₁ [* P₂ *]) (h₂ : [* P₂ *] p₂ [* P₃ *]) :
  [* P₁ *] p₁ ;; p₂ [* P₃ *] :=
sorry

/- 2.5. Prove the rule for `ite`. This requires `c s ∨ ¬ c s`. `classical.em (c s)` provides a
proof, even when `c` is not decidable. -/

lemma ite_intro (h₁ : [* λs, P s ∧ c s *] p₁ [* Q *]) (h₂ : [* λs, P s ∧ ¬ c s *] p₂ [* Q *]) :
  [* P *] ite c p₁ p₂ [* Q *] :=
sorry

/- 2.6. Try to prove the rule for `while`.

Before we prove our final goal, we introduce an auxiliary proof. This proof requires
well-founded induction. When using `while_intro.aux` as induction hypothesis we recommend
to do it directly after proving that the argument is less than `n`:

    have ih : ∃u, (while c p, t) ⟹ u ∧ I u ∧ ¬c u :=
      have M < n := ..., -- necessary for Lean to figure out the well-founded induction
      while_intro.aux M ...,

Similar to `ite`, this requires `c s ∨ ¬ c s`. `classical.em (c s)` provides a proof. -/

lemma while_intro.aux
  (I : state → Prop)
  (V : state → ℕ)
  (h_inv : ∀n, [* λs, I s ∧ c s ∧ V s = n *] p [* λs, I s ∧ V s < n *]) :
  ∀n s, V s = n → I s → ∃t, (while c p, s) ⟹ t ∧ I t ∧ ¬ c t
| n s V_eq hs :=
sorry

lemma while_intro
  (I : state → Prop)  -- invariant in the loop
  (V : state → ℕ)  -- variant in the loop body (a.k.a. termination measure)
  (h_inv : ∀n, [* λs, I s ∧ c s ∧ V s = n *] p [* λs, I s ∧ V s < n *]) :
  [* I *] while c p [* λs, I s ∧ ¬ c s *] :=
sorry

end total_hoare

end lecture
