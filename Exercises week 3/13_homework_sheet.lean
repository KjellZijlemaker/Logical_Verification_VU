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
  intros ex p,
  intros a b,
  apply or.elim,
  apply ex,
  intro c,
  apply c,
  intro d,
  apply b,
  intro p,
  apply false.elim,
  apply d,
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

lemma dn_em_imp : excluded_middle → double_negation :=
begin
  intros a b c,
  apply em_imp_peirce,
  intro l,
  apply or.elim,
  apply a,
  intro l,
  apply l,
  intro notl,
  apply or.intro_right,
  intro l,
  apply notl,
  apply or.intro_left,
  assumption,
  intro k,
  apply k,
  apply or.elim,
  apply a,
  apply k,
  intro notb,
  apply false.elim,
  apply c,
  assumption
end


lemma imp_em_peirce :  peirce → excluded_middle := 
begin
  intros a b,
  apply dn_em_imp,
  intro l,
  apply a,
  intro s,
  apply or.inl,
  apply s,
  apply dn_imp_em,
  intro newl,
  intro double,
  apply a,
  intro b,
  apply false.elim,
  apply double,
  apply b,
  apply false.elim,
  apply double,
  intro s,
  apply double,
  apply b,
  assumption,
  intro s,
  apply s,
  apply or.inr,
  intro l,
  apply s,
  apply or.inl,
  assumption
end

-- lemma peirce_dn_imp :  double_negation → peirce:=
-- begin
-- intros a b c,
-- intro s,
-- apply peirce_imp_dn,
-- intro ex,
-- intros l q,
-- apply q,
-- intro ex,

-- end
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


/- 2.2. Redo the above proof, this time using structured proofs (with `assume`, `have`, and `show`)
for the two subcases emerging from the introduction rule for `↔`. -/

example {α} (p q : α → Prop) : (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
begin
  apply iff.intro,
  assume hpq,
  apply and.intro,
  assume ah,
  have b := and.left (hpq ah),
  show p ah, from b,
  assume bh,
  have c := and.right (hpq bh),
  show q bh, from c,
  assume hpq,
  assume dh,
  apply and.intro,
  have e := and.left hpq dh,
  show p dh, from e,
  have f := and.right hpq dh,
  show q dh, from f
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
| [] := by refl
| (x :: xs) := 
begin 
simp[reverse],
simp[list.reverse],
simp[list.reverse_core],
induction xs,
simp[reverse, list.reverse_core],
simp[reverse,list.reverse_core],
simp[list.reverse],

end
