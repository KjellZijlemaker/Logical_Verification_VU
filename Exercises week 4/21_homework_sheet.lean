/- Homework 2.1: Functional Programming — Lists -/

/- Question 1: Replicating an element -/

/- 1.1. Define a function `replicate` that takes an element `a` of type `α` and a natural number `n`
and that returns a list of length `n` consisting of `n` occurrences of `a`: `[a, ..., a]` -/

-- enter your definition here

#check list.length

/- 1.2. State and prove that `replicate a n` has length `n`. -/

-- enter your answer here

/- 1.3. State and prove that `list.map f (replicate a n)` is the same as `replicate (f a) n`. Make
sure to state the result as generally as possible. -/

-- enter your answer here

/- 1.4. State and prove that `replicate a m ++ replicate a n` equals `replicate a (m + n)`.

There are many ways to prove this. A calculational proof might be useful here to manipulate the
expression step by step (but is not mandatory). -/

-- enter your answer here

/- 1.5. State and prove that `reverse` has no effect on `replicate a n`.

Hint: If you get stuck in the induction step, this may indicate that you first need to prove
another lemma, also by induction. -/

def reverse {α : Type} : list α → list α
| []        := []
| (x :: xs) := reverse xs ++ [x]

-- enter your answer here


/- Question 2: Binary relations -/

/- The following questions concern modeling properties of binary relations (actually, curried binary
predicates). To avoid repeating `α` and `R` in each definition, we use a section and fix them
locally in the section. -/

section

parameter {α : Type}
parameter R : α → α → Prop

def irreflexive_rel := ∀x : α, ¬ R x x
def antisymmetric_rel := ∀x y : α, R x y → ¬ R y x
def transitive_rel := ∀x y z : α, R x y → R y z → R x z

/- 2.1. Prove that antisymmetry implies irreflexivity.

Hint: It may help to first think abstractly why this is the case before trying to prove it in Lean.
Alternatively, try to see this as a video game and use `intros` and `apply` until you have defeated
the boss. There exists a fairly short `apply`-style proof. -/

lemma antisymmetric_rel_implies_irreflexive_rel : antisymmetric_rel → irreflexive_rel :=
sorry

/- 2.2. Define `symmetric_rel` as the proposition stating that `R` is symmetric—that is, if `x`
and `y` are related via `R`, then `y` and `x` are related via `R`. -/

-- enter your definition here

/- 2.3. State and prove the property that any irreflexive and transitive relation is
antisymmetric. -/

-- enter your answer here

end

/- Notice that each of the definition takes `α` as implicit argument and `R` as explicit argument.
Everything we have defined and proved above is now available in a very general form. -/

#check irreflexive_rel
#check antisymmetric_rel
#check transitive_rel

#check antisymmetric_rel_implies_irreflexive_rel
