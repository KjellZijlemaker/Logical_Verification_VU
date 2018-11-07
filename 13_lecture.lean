/- Lecture 1.3: Basics — More Logic and Proofs -/

/- Logical connectives and quantifiers -/

-- introduction rules
#check true.intro
#check not.intro
#check and.intro
#check or.intro_left
#check or.intro_right
#check iff.intro
#check exists.intro

-- elimination rules
#check false.elim
#check and.elim_left
#check and.elim_right
#check or.elim
#check exists.elim

-- aliases
#check and.left
#check and.right

-- definition of `¬` and related lemmas
#print not
#check classical.em
#check classical.by_contradiction

example (p q : Prop) : p ∧ q → p := and.elim_left

example (p q : Prop) : p ∧ q → q ∧ p :=
assume hpq : p ∧ q,
have hp : p := and.left hpq,
have hq : q := and.right hpq,
show q ∧ p, from and.intro hq hp

-- conjunction (`and`)

example (p q : Prop) : p ∧ q → q ∧ p :=
λhpq : p ∧ q,
  (λhp : p,
    (λhq : q,
      (and.intro hq hp : q ∧ p))
    (and.right hpq))
  (and.left hpq)

example : ∀p q : Prop, p ∧ q → q ∧ p :=
begin
  intros _ _ hpq,
  exact and.intro (and.right hpq) (and.left hpq)
end

example (p q : Prop) (h : p ∧ q) : q ∧ p :=
⟨h.right, h.left⟩

example : ∀p q : Prop, p ∧ q → q ∧ p :=
begin
  intros _ _ hpq,
  apply and.intro,
  exact hpq.right,
  exact hpq.left
end

-- disjunction (`or`)

example (p q : Prop) : p ∨ q → q ∨ p
| (or.inl h) := or.inr h
| (or.inr h) := or.inl h

example (p q : Prop) : p ∨ q → q ∨ p :=
begin
  intros hpq,
  apply (or.elim hpq),
  { intros h, apply or.inr h },
  { intros h, apply or.inl h }
end

-- implication (`imp`)

example (p q : Prop) : p → q → p :=
assume hp hq,
show p, from hp

-- modus ponens (elimination of implication)

example (p q : Prop) (h : p → q) (hp : p) : q :=
h hp

example (p q : Prop) (h : p → q) (hp : p) : q :=
begin
  apply h,
  exact hp
end

example (p q : Prop) (h : p → q) (hp : p) : q :=
begin
  apply h,
  assumption
end

-- proof of negation

example (p : Prop) : p → ¬¬ p :=
begin
  dunfold not,
  intro hp,
  apply not.intro,
  intro hnp,
  apply hnp,
  exact hp
end

example (p : Prop) : p → ¬¬ p :=
begin
  intros hp hnp,
  refine hnp _,
  exact hp
end

-- proof by contradiction

example (p : Prop) : ¬¬ p → p :=
begin
  intro hnnp,
  apply classical.by_contradiction,
  apply hnnp
end

example (p : Prop) : ¬¬ p → p :=
begin
  intro,
  apply classical.by_contradiction,
  assumption
end


/- Arithmetic calculations -/

-- `#mul` in Visual Studio Code's command palette
#check two_mul

example (m n : ℕ) : 2 * m + n = m + n + m :=
calc 2 * m + n = (m + m) + n : by rw two_mul
... = m + n + m : by ac_refl
