/- Exercise 3.1: Program Semantics — Operational Semantics -/

/- We start by repeating some material from the lecture. We use the same `program` syntax and the
big-step semantics as presented in the lecture. -/

attribute [pattern] or.intro_left or.intro_right

inductive program (σ : Type) : Type
| skip {} : program
| assign  : (σ → σ) → program
| seq     : program → program → program
| ite     : (σ → Prop) → program → program → program
| while   : (σ → Prop) → program → program

namespace program

variables {σ : Type} {c : σ → Prop} {f : σ → σ} {p p₀ p₁ p₂ : program σ} {s s₀ s₁ s₂ t u : σ}

inductive big_step : (program σ × σ) → σ → Prop
| skip {s} :
  big_step (skip, s) s
| assign {f s} :
  big_step (assign f, s) (f s)
| seq {p₁ p₂ s u} (t) (h₁ : big_step (p₁, s) t) (h₂ : big_step (p₂, t) u) :
  big_step (seq p₁ p₂, s) u
| ite_true {c : σ → Prop} {p₁ p₀ s t} (hs : c s) (h : big_step (p₁, s) t) :
  big_step (ite c p₁ p₀, s) t
| ite_false {c : σ → Prop} {p₁ p₀ s t} (hs : ¬ c s) (h : big_step (p₀, s) t) :
  big_step (ite c p₁ p₀, s) t
| while_true {c : σ → Prop} {p s u} (t) (hs : c s) (hp : big_step (p, s) t)
  (hw : big_step (while c p, t) u) :
  big_step (while c p, s) u
| while_false {c : σ → Prop} {p s} (hs : ¬ c s) : big_step (while c p, s) s

infix ` ⟹ `:110 := big_step

/- We copy also the inversion rules from the lecture. Do not prove these. -/

@[simp] lemma big_step_skip_iff :
  (skip, s) ⟹ t ↔ t = s := sorry
@[simp] lemma big_step_assign_iff :
  (assign f, s) ⟹ t ↔ t = f s := sorry
@[simp] lemma big_step_seq_iff :
  (seq p₁ p₂, s) ⟹ t ↔ (∃u, (p₁, s) ⟹ u ∧ (p₂, u) ⟹ t) := sorry
@[simp] lemma big_step_ite_iff :
  (ite c p₁ p₀, s) ⟹ t ↔ ((c s ∧ (p₁, s) ⟹ t) ∨ (¬ c s ∧ (p₀, s) ⟹ t)) := sorry
lemma big_step_while_iff :
  (while c p, s) ⟹ t ↔ (∃u, c s ∧ (p, s) ⟹ u ∧ (while c p, u) ⟹ t) ∨ (¬ c s ∧ t = s) := sorry
@[simp] lemma big_step_while_true_iff (hs : c s) :
  (while c p, s) ⟹ t ↔ (∃u, (p, s) ⟹ u ∧ (while c p, u) ⟹ t) := sorry
@[simp] lemma big_step_while_false_iff (hs : ¬ c s) :
  (while c p, s) ⟹ t ↔ t = s := sorry


/- Question 1: Program equivalence -/

/- For this question, we introduce the notation of program equivalence `p₁ ≈ p₂`. `≈` is entered as
`\approx`. -/

def program_equiv (p₁ p₂ : program σ) : Prop :=
∀s t, (p₁, s) ⟹ t ↔ (p₂, s) ⟹ t

local infix ` ≈ ` := program_equiv

/- Program equivalence is a equivalence relation, i.e. it is reflexive, symmetric, and
transitive. -/

@[refl] lemma program_equiv.refl :
  p ≈ p :=
assume s t, by refl

@[symm] lemma program_equiv.symm :
  p₁ ≈ p₂ → p₂ ≈ p₁ :=
assume h s t, (h s t).symm

@[trans] lemma program_equiv.trans {p₃} (h₁₂ : p₁ ≈ p₂) (h₂₃ : p₂ ≈ p₃) :
  p₁ ≈ p₃ :=
assume s t, iff.trans (h₁₂ s t) (h₂₃ s t)


/- 1.1. Prove the following program equivalences. -/

lemma program_equiv_seq_skip1 {p : program σ} : seq skip p ≈ p :=
begin
assume s t, 
apply iff.intro,
assume l,
cases p,
simp [program_equiv],
-- cases l_h₂,
simp at l,
cases l,
cases l_h,
cases l_h_left,
assumption,
simp,
cases l,
repeat {cases l_h₁},
repeat {cases l_h₂},
refl,
cases l,
cases l_h₂,
cases l_h₂_h₂,
simp,
cases l_h₂_h₂,
cases l_h₂_h₁,
simp,
cases l_h₁,
cases l_h₂_h₁ ,
cases l_h₁



end

lemma program_equiv_seq_skip2 {p : program σ} : seq p skip ≈ p :=
begin
assume s t,
apply iff.intro,
simp[program_equiv],
intro e,
cases p,
simp,
simp at e,
cases e,
cases e_h,
cases e_h_left,
cases e_h_right,
assumption,
simp at e,
cases e,
cases e_h,
cases e_h_left,
cases e_h_right,
simp,
simp at e,
cases e,
cases e_h,
cases e_h_left,
cases e_h_right,
simp,
cases e_h_left_h,
end


lemma program_equiv_seq_congr {p₁ p₂ p₃ p₄ : program σ}
  (h₁₂ : p₁ ≈ p₂) (h₃₄ : p₃ ≈ p₄) :
  seq p₁ p₃ ≈ seq p₂ p₄ :=
sorry

lemma program_equiv.ite_seq_while :
  ite c (seq p (while c p)) skip ≈ while c p :=
sorry

/- 1.2. Prove one more equivalence. `@id σ` is the identity function on states. -/

lemma program_equiv.skip_assign_id : assign (@id σ) ≈ skip :=
sorry

/- 1.3. Why do you think `@id σ` is necessary, as opposed to `id`? -/

/- Answer: enter your answer here. -/

end program


/- Question 2: The guarded command language (GCL) -/

/- In 1976, E. W. Dijkstra introduced the guarded command language, as a language with
built-in nondeterminism. Its grammar is as follows:

    p  ::=  x := e        -- assignment
         |  assert b      -- assertion
         |  p ; p         -- sequential composition
         |  p | ... | p   -- nondeterministic choice
         |  loop p        -- nondeterministic iteration

Assignment and sequential composition are as in the WHILE language. The other statements have the
following semantics:

* `assert b` aborts if `b` evaluates to false; otherwise, the command is a no-op.

* `p | ... | p` chooses **any** of the branches and executes it, ignoring the other branches.

* `loop p` executes `p` **any** number of times.

In Lean, GCL is captured by the following inductive type: -/

inductive gcl (σ : Type) : Type
| assign : (σ → σ) → gcl
| assert : (σ → Prop) → gcl
| seq    : gcl → gcl → gcl
| choice : list gcl → gcl
| loop   : gcl → gcl

namespace gcl

variable {σ : Type}
variables {c : σ → Prop} {f : σ → σ} {p p₀ p₁ p₂ : gcl σ} {ps : list (gcl σ)} {s s₀ s₁ s₂ t u : σ}

/- The big-step semantics is defined as follows: -/

inductive big_step : (gcl σ × σ) → σ → Prop
| assign {f s} :
  big_step (assign f, s) (f s)
| assert {c : σ → Prop} {s} (hs : c s) :
  big_step (assert c, s) s
| seq {p₁ p₂ s u} (t) (h₁ : big_step (p₁, s) t) (h₂ : big_step (p₂, t) u) :
  big_step (seq p₁ p₂, s) u
| choice {ps : list (gcl σ)} {s t} (i : ℕ) (hi : i < list.length ps)
  (h : big_step (list.nth_le ps i hi, s) t) :
  big_step (choice ps, s) t
| loop_base {p s} :
  big_step (loop p, s) s
| loop_step {p s t} (u) (h₁ : big_step (p, s) u) (h₂ : big_step (loop p, u) t) :
  big_step (loop p, s) t

/- Some convenience syntax: -/

infix ` ~> `:110 := big_step

/- 2.1. Prove the following inversion rules, as we did in the lecture for the WHILE language. -/

@[simp] lemma big_step_assign : (assign f, s) ~> t ↔ t = f s :=
sorry

@[simp] lemma big_step_assert : (assert c, s) ~> t ↔ (t = s ∧ c s) :=
sorry

@[simp] lemma big_step_seq : (seq p₁ p₂, s) ~> t ↔ (∃u, (p₁, s) ~> u ∧ (p₂, u) ~> t) :=
sorry

lemma big_step_loop : (loop p, s) ~> t ↔ (s = t ∨ (∃u, (p, s) ~> u ∧ (loop p, u) ~> t)) :=
sorry

@[simp] lemma big_step_choice :
  (choice ps, s) ~> t ↔ (∃(i : ℕ) (hi : i < list.length ps), (list.nth_le ps i hi, s) ~> t) :=
sorry

/- 2.2. Fill in the translation below of a deterministic program to a GCL program, by filling in the
`sorry` placeholders below. -/

def of_program : program σ → gcl σ
| program.skip          := assign id
| (program.assign f)    :=
  sorry
| (program.seq p₁ p₂)   :=
  sorry
| (program.ite c p₁ p₂) :=
  choice [
    seq (assert c) (of_program p₁),
    seq (assert (λs, ¬ c s)) (of_program p₂)
  ]
| (program.while c p)   := seq (loop (seq (assert c) (of_program p))) (assert (λs, ¬ c s))

/- 2.3. Prove that `of_program` is correct, in the sense that whenever the deterministic program `p`
can make a big step, the corresponding GCL program makes a big step.

This is a difficult exercise. Try to get as far as possible.

**Hints:**

* In the each induction subgoal, use `cases h` on an equality `h : (p, s) = (q, t)`. When one side
is a variable, it will be replaced by the other side. In our case, one side is always a variable.

* Use `specialize h rfl` to instantiate a hypothesis, i.e. to replace a hypothesis of the form
`h : ∀{x y}, (x, y) = (p, s) → q x y` with `h : q p s`.

* At some point you need to prove statements such as `0 < 1 + 1`. Here, you can use use the
`dec_trival` proof term (e.g. in tactic mode, you must write `exact dec_trivial`)

* You need to use `cases` in the `while_true` case, to cope with a hypothesis of the form
`h : of_program (while c p, s) ~> t`. This breaks the hypothesis down and will allow you to retrieve
the intermediate states and steps.

* You may want to use lemmas from the `program` namespace, e.g. the inversion rules
(`program.big_step_while_iff`, etc.). -/

lemma big_step_of_program {p : program σ} {s t} :
  (p, s) ⟹ t → (of_program p, s) ~> t :=
begin
  /- The term `(p, s)` needs to be replaced by a variable. We use the same tools as in the lecture:

  * `generalize` replaces a term in our goal by a new variable and an equality assumption.

  * `generalizing p s` tells the `induction` tactic that `p` and `s` should be quantified. -/
  generalize eq : (p, s) = ps,
  intro h,
  induction h generalizing p s;
    cases eq;
    clear eq,
  { simp [of_program] },
  { sorry },
  { sorry },
  { sorry },
  { sorry },
  { sorry },
  { sorry }
end

end gcl
