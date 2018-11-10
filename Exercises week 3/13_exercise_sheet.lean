/- Exercise 1.3: Basics — More Logic and Proofs -/

/- Question 1: Logical symbols -/

/- For all of the following exercises, it can help to unfold the definition of `not`. This can be
achieved using the tactic `dunfold not`. -/

/- 1.1. Prove the following propositions, using whichever style you prefer. -/

example (p q : Prop) : q → p → p :=
assume hq: q,
assume hp: p,
show p, from hp


example (p q r : Prop) : (p → q → r) → (p → q) → p → r :=
begin
assume p q r,
apply p,
exact r,
apply q,
exact r
end

/- This one is a bit tricky. You will need to use the assumption twice. -/
lemma weak_peirce (p q : Prop) : ((((p → q) → p) → p) → q) → q :=
begin
assume p,
apply p,
assume k,
apply k,
assume l,
apply p,
assume s,
exact l
end




lemma contrapositive (p q : Prop) : (p → q) → ¬ q → ¬ p :=
begin
dunfold not,
assume p q,
assume k,
apply q,
apply p,
exact k
end

/- 1.2. Intuitionistic logic is extended to classical logic by assuming a classical axiom. There
are several possibilities for the choice of a classical axiom. In this practical work we show the
logical equivalence of three different classical axioms.

For this exercise, avoid using lemmas from Lean's `classical` namespace, because this would defeat
the purpose of the exercise.

Below, Peirce is pronounced like the English word "purse". -/

def excluded_middle := ∀p : Prop, p ∨ ¬ p
def peirce := ∀p q : Prop, ((p → q) → p) → p
def double_negation := ∀p : Prop, ¬¬ p → p

/- Hint: You will need `or.elim` and `false.elim` below. -/

lemma em_imp_peirce : excluded_middle → peirce :=
begin
assume p q s l,
apply or.elim,
apply p,
apply l,
intro sh,
apply false.elim,
apply sh,
intro qh,
apply or.elim,
apply p,
apply false.elim,
intro l,
apply or.elim,
apply p,
apply not sh





end

/- Hint: Try instantiating `q` with `false` in Peirce's law. -/

lemma peirce_imp_dn : peirce → double_negation :=
begin
  intros p not q,
  apply p,
  intro s,
  apply false.elim,
  apply q,
  apply s,
  apply p not,
  intro l,
  apply l,
  apply false.elim,
  apply q,
  intro sh,
  apply p,
  intro lh,
  apply s,
  apply lh,
  apply s,
  assumption,
  assumption,
  assumption
end


/- We will do the missing implication in the homework: -/

example : double_negation → excluded_middle := sorry   -- not now


/- Question 2: Calculational proofs -/

/- 2.1. Write the following proof using `calc`.

  (a + b) * (a + b)
  = a * (a + b) + b * (a + b)
  = a * a + a * b + b * a + b * b
  = a * a + a * b + a * b + b * b
  = a * a + 2 * a * b + b * b

Hint: You might need `rw`, `simp`, `ac_refl`, and the lemmas `mul_add`, `add_mul`, and `two_mul`.
-/

lemma binomial_square (a b : ℕ) : (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
calc (a + b) * (a + b) 
         = a * (a + b) + b * (a + b)      : by simp[mul_add, add_mul]
     ... = a * a + a * b + b * a + b * b  : by simp[mul_add]
     ... = a * a + a * b + a * b + b * b  : by ac_refl
     ... = a * a + 2 * a * b + b * b      : begin simp[two_mul], simp[add_mul] end

/- 2.2. Fill in the gaps in the following proof.

In part 4 of the course, we will see Lean's mathematical library (mathlib), which contains useful
tactics to reason about arithmetic. Without mathlib, we are forced to take baby steps.

Hint: You might need `rw`, `simp`, `ac_refl`, and the lemmas `mul_add` and `add_mul` (as well as
the induction hypothesis, other local facts, and the definition of `sum_upto`).

Warning: Keep an eye on the orange bars indicating nontermination (or very slow proofs).
-/

def sum_upto (f : ℕ → ℕ) : ℕ → ℕ
| 0       := f 0
| (m + 1) := sum_upto m + f (m + 1)

lemma sum_upto_square_eq : ∀m : ℕ, 6 * sum_upto (λn, n * n) m = m * (m + 1) * (2 * m + 1)
| 0       := by refl
| (m + 1) :=
  calc 6 * sum_upto (λn, n * n) (m + 1) =
    6 * sum_upto (λn, n * n) m + 6 * (m + 1) * (m + 1) :
    begin simp[sum_upto, add_mul], refl end
  ... = m * (m + 1) * (2 * m + 1) + 6 * (m + 1) * (m + 1) :
    sorry
  ... = (m + 1) * (m * (2 * m + 1)) + (m + 1) * (6 * (m + 1)) :
    sorry
  ... = (m + 1) * (m * (2 * m + 1) + 6 * (m + 1)) :
    sorry
  ... = (m + 1) * (m + 1 + 1) * (2 * (m + 1) + 1) :
    have m * (2 * m + 1) + 6 * (m + 1) = (m + 1 + 1) * (2 * (m + 1) + 1) :=
      have four : 4 = 2 * 2 :=
        sorry,
      have six : 6 = 2 + 4 :=
        sorry,
      calc m * (2 * m + 1) + 6 * (m + 1) = 2 * m * m + m + 6 * m + 6 :
        sorry
      ... = 2 * m * m + 2 * m + 4 * m + m + 2 + 4 :
        sorry
      ... = (m + 1 + 1) * (2 * (m + 1) + 1) :
        sorry
    by rw this; ac_refl
