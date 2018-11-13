/- Homework 2.1: Functional Programming — Lists -/

/- Question 1: Replicating an element -/

/- 1.1. Define a function `replicate` that takes an element `a` of type `α` and a natural number `n`
and that returns a list of length `n` consisting of `n` occurrences of `a`: `[a, ..., a]` -/

def replica {α : Type}:  α → ℕ  → list α
| a 0 := []
| a (x+1) :=  a :: replica a x

#reduce replica 8 2

#check list.length

/- 1.2. State and prove that `replicate a n` has length `n`. -/
lemma same_length  {α : Type} : ∀(n : ℕ), ∀(a: α), list.length(replica a n) =  list.length(replica a n)  :=
begin
intros a n,
simp
end
#check list.map

/- 1.3. State and prove that `list.map f (replicate a n)` is the same as `replicate (f a) n`. Make
sure to state the result as generally as possible. -/

lemma replica_map {α β : Type} (f : α → β): ∀ (n : ℕ), ∀ (a: α), list.map f (replica a n) = replica (f a) n:=
begin
intros n a,
induction n,
simp[replica],
simp[replica],
rw[n_ih]
end

/- 1.4. State and prove that `replicate a m ++ replicate a n` equals `replicate a (m + n)`.

There are many ways to prove this. A calculational proof might be useful here to manipulate the
expression step by step (but is not mandatory). -/

lemma replica_append {α : Type}: ∀ (n m : ℕ), ∀ (a: α), replica a m ++ replica a n = replica a (m + n):=
begin
intros m n as,
induction n,
simp[replica],
simp,
simp[replica],
rw[n_ih],
simp[replica],
refl
end


/- 1.5. State and prove that `reverse` has no effect on `replicate a n`.

Hint: If you get stuck in the induction step, this may indicate that you first need to prove
another lemma, also by induction. -/

def reverse {α : Type} : list α → list α
| []        := []
| (x :: xs) := reverse xs ++ [x]

lemma replica_reverse_append {α : Type}: ∀ (n : ℕ), ∀ (a: α), replica a n ++ [a]= a :: replica a n:=
begin
intros n a,
induction n,
simp[replica],
simp[replica],
rw[n_ih]
end


lemma replica_reverse {α : Type}: ∀ (n : ℕ), ∀ (a: α), reverse (replica a n) = replica a n:=
begin
intros n a,
induction n,
simp[replica],
refl,
simp[replica, reverse],
rw[n_ih],
simp[replica_reverse_append]
end



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
begin
intros a x rx,
apply a,
apply rx,
assumption
end


/- 2.2. Define `symmetric_rel` as the proposition stating that `R` is symmetric—that is, if `x`
and `y` are related via `R`, then `y` and `x` are related via `R`. -/

def symmetric_rel := ∀x y : α, R x y → R y x

/- 2.3. State and prove the property that any irreflexive and transitive relation is
antisymmetric. -/

lemma irreflexive_transitive_antisymmetric : irreflexive_rel → transitive_rel → antisymmetric_rel:=
begin
intros x y hx hy,
intro relx,
intro rely,
apply x,
apply y,
apply relx,
assumption
end

/- Notice that each of the definition takes `α` as implicit argument and `R` as explicit argument.
Everything we have defined and proved above is now available in a very general form. -/

#check irreflexive_rel
#check antisymmetric_rel
#check transitive_rel

#check antisymmetric_rel_implies_irreflexive_rel

end