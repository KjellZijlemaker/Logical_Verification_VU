/- Exercise 2.2: Functional Programming — Trees -/

/- Question 1: Even and odd -/

/- 1.1. Define an inductive predicate `even` on `ℕ` that is true for even numbers and false for odd
numbers.

Hint: Your predicate should have two introduction rules, one for the 0 case and one for the `n + 2`
case. -/

-- enter your definition here

/- 1.2. Prove that 0, 2, 4, and 6 are even. -/

-- enter your answer here

def odd (n : ℕ) : Prop :=
  ¬ even n

/- 1.3. Prove that 1 is odd and register this fact as a `simp` rule.

Hint: `cases` is useful to reason about hypotheses of the form `even ...`. -/

-- enter your answer here

/- 1.4. Prove that 3, 5, and 7 are odd. -/

-- enter your answer here

/- 1.5. Complete the following proof by structural induction. -/

lemma even_two_times :
  ∀m : ℕ, even (2 * m)
:= sorry

/- 1.6. Complete the following proof by rule induction.

Hint: You can use the `cases` tactic or `match ... with` to destruct an existential quantifier and
extract the witness. -/

lemma even_imp_exists_two_times :
  ∀n : ℕ, even n → ∃m, n = 2 * m
| _ even.zero          := ⟨0, by simp⟩
| _ (even.add_two n h) :=
sorry

/- 1.7. Using `even_two_times` and `even_imp_exists_two_times`, prove the following equivalence. -/

lemma even_iff_exists_two_times (n : ℕ) :
  even n ↔ ∃m, n = 2 * m :=
sorry


/- Question 2: Binary trees -/

namespace my_bin_tree

/- Recall the binary trees from the lecture. As usual, we omit the proofs using `sorry`. -/

inductive tree (α : Type) : Type
| empty {} : tree
| node (a : α) (l : tree) (r : tree) : tree

export tree (empty node)

def mirror {α : Type} : tree α → tree α
| empty        := empty
| (node a l r) := node a (mirror r) (mirror l)

lemma empty_mirror_iff {α : Type} : ∀t : tree α, mirror t = empty ↔ t = empty := sorry
lemma mirror_mirror {α : Type} : ∀t : tree α, mirror (mirror t) = t := sorry

inductive is_full {α : Type} : tree α → Prop
| empty : is_full empty
| node (a : α) (l r : tree α) (hl : is_full l) (hr : is_full r)
    (empty_iff : l = empty ↔ r = empty) :
    is_full (node a l r)

lemma is_full_singleton {α : Type} (a : α) : is_full (node a empty empty) := sorry
lemma is_full_mirror {α : Type} : ∀t : tree α, is_full t → is_full (mirror t) := sorry

/- 2.1. State and prove the converse of `is_full_mirror`. -/

-- enter your answer here

/- 2.2. Define a function that counts the number of constructors (`empty` or `node`) in a tree. -/

def count {α : Type} : tree α → ℕ
:= sorry

end my_bin_tree


/- Question 3: λ-terms -/

namespace my_lambda_term

/- 3.1. Define an inductive type corresponding to the untyled λ-terms, as given by the following
context-free grammar:

<lam> ::= 'var' <string>
        | 'abs' <string> <lam>
        | 'app' <lam> <lam>
-/

-- enter your definition here

/- 3.2. Define an inductive predicate `is_βnf` that determines whether a lambda term is in β-normal
form (https://en.wikipedia.org/wiki/Beta_normal_form). -/

-- enter your answer here

/- 3.3. Register a textual representation of the type `lam`, as we did for Huffman trees in the
lecture. -/

-- enter your answer here

end my_lambda_term
