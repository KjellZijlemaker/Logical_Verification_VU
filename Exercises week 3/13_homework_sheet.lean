/- Homework 1.3: Basics — More Logic and Proofs -/

/- Question 1: Logical connectives -/

/- 1.1. Prove the following property about double negation.

Hint: Notice and exploit the similarity with the weak Peirce law from the exercises. Also, you will
need the elimination rule for `false` at a key point. -/

lemma herman (p : Prop) : ¬¬ (¬¬ p → p) :=
begin
  dunfold not,
  intro ph,
  apply ph,
  intro lh,
  apply false.elim,
  apply lh,
  intro kh,
  apply ph,
  intro sh,
  assumption
end




/- 1.2. Prove the missing link in our chain of classical axiom implications.

Hint: You will need to apply the double negation hypothesis for `p ∨ ¬ p`. You will also need the
left and right introduction rules for `or` at some point.
-/

def excluded_middle := ∀p : Prop, p ∨ ¬ p
def peirce := ∀p q : Prop, ((p → q) → p) → p
def double_negation := ∀p : Prop, ¬¬ p → p

lemma dn_imp_em : double_negation → excluded_middle :=
begin
  intros ph qh,
  apply ph,
  intro lh,
  apply false.elim,
  apply ph,
  intro sh,
  apply false.elim,
  apply lh,
  apply or.inr,
  intro th,
  apply lh,
  apply or.inl,
  assumption
end

-- these are copied from the exercise; there is no need to prove them again
lemma em_imp_peirce : excluded_middle → peirce := 
begin
intros a b c d,
apply d,
intro e,
apply or.elim,
apply a c,
intro f,
exact f,
intro g,
apply false.elim,
apply g,
assumption



end

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

/- 1.3. We have proved three of the six possible implications between `excluded_middle`, `peirce`,
and `double_negation`. State and prove the three missing implications, exploiting the three theorems
we have already proved. -/

-- enter your solution here


/- Question 2: Predicate logic -/

/- 2.1. Prove the distributivity of `∀` over `∧` using `intro(s)`, `apply`, and `exact`. -/



example {α} (p q : α → Prop) :
 (∀x, p x ∧ q x) ↔  (∀x, p x) ∧ (∀x, q x) :=
begin
apply iff.intro,
intro ph,
apply and.intro,
intro sh,
apply and.elim,
apply ph,
exact sh,
intros lh qh,
exact lh,
intro eh,
apply and.elim,
apply ph,
exact eh,
intros ah bh,
exact bh,
intros newph newsh,
apply and.intro,
apply and.elim,
apply newph,
intros newph newsh,
apply newph,
apply and.elim,
apply newph,
intros qh yh,
apply yh
end 

example (p q : Prop) : p ∧ q → q ∧ p :=
begin
  intro h,
  cases h with hp hq,
  split,
  show q, from hq,
  show p, from hp
end

/- 2.2. Redo the above proof, this time using structured proofs (with `assume`, `have`, and `show`)
for the two subcases emerging from the introduction rule for `↔`. -/

example {α} (p q : α → Prop) : (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
begin
  apply iff.intro,
  begin
    assume hs,

    
    -- have hs, from and.elim,
  end

  end


/- Question 3: The reverse of a list, revisited -/

def reverse {α} : list α → list α
| []        := []
| (x :: xs) := reverse xs ++ [x]

-- taken from lecture 1.2
lemma reverse_append {α} : ∀xs ys : list α, reverse (xs ++ ys) = reverse ys ++ reverse xs:=
begin
intro s,
induction s,
simp[reverse],
simp[reverse],
intro l,
rw[s_ih],
simp
end

/- 3.1. Prove the induction step in the proof below using the **calculational style**, following
this proof sketch:

  reverse (reverse (x :: xs))
=     { by definition of `reverse` }
  reverse (reverse xs ++ [x])
=     { using the lemma `reverse_append` }
  reverse [x] ++ reverse (reverse xs)
=     { by the induction hypothesis }
  reverse [x] ++ xs
=     { by definition of `++` and `reverse` }
  [x] ++ xs
=     { by definition of `++` }
  x :: xs
-/

lemma reverse_reverse {α} : ∀xs : list α, reverse (reverse xs) = xs
| [] := by refl
| (x :: xs) :=
calc reverse  (reverse (x :: xs)) 
      =       x::xs                                 :     by simp[reverse, reverse_append, reverse, reverse_reverse xs]
  ... =       reverse (reverse xs ++ [x])           :     by simp[reverse_append, reverse, reverse_reverse xs]
  ... =       reverse [x] ++ reverse (reverse xs)   :     by simp[reverse, reverse_append]
  ... =       reverse [x] ++ xs                     :     by simp[reverse, reverse_reverse xs]
  ... =       [x] ++ xs                             :     by simp[reverse]
  ... =       x :: xs                               :     by simp[reverse]

/- 3.2 (**optional bonus**). Lean's library includes an operation called `list.reverse`. Its
implementation is optimized to be tail-recursive, by means of an accumulator. Prove that the
optimized `list.reverse` behaves in the same way as our simple `reverse` implementation.

To see the definition of `list.reverse`, hover over its name below while holding the Control or
Command key pressed and click the name.
-/

#check list.reverse

lemma list_reverse_eq_reverse {α} : ∀xs : list α, list.reverse xs = reverse xs
:= sorry
