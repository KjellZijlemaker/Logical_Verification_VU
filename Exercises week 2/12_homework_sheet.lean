/- Homework 1.2: Basics — Proofs -/

/- Question 1: Drop and Take -/

def drop {α : Type} : ℕ → list α → list α
| 0       xs        := xs
| (_ + 1) []        := []
| (m + 1) (x :: xs) := drop m xs

#reduce drop 2 [2,4,6, 8]

/- 1.1. Define `take`. -/

/- To avoid bad surprises in the proofs, we recommend that you follow the same recursion pattern as
for `drop` above. -/

def take {α : Type} : ℕ → list α → list α
| 0             xs      :=      []
| (_ + 1)       []      :=      []
| (m + 1)  (x::xs) :=      [x] ++ take m xs 


#reduce take 0 [3, 7, 11]   -- expected: []
#reduce take 1 [3, 7, 11]   -- expected: [3]
#reduce take 2 [3, 7, 11]   -- expected: [3, 7]
#reduce take 3 [3, 7, 11]   -- expected: [3, 7, 11]
#reduce take 4 [3, 7, 11]   -- expected: [3, 7, 11]

#reduce take 3[]
-- when `#reduce` fails for some obscure reason, try `#eval`:
#eval take 2 ["a", "b", "c"]   -- expected: ["a", "b"]

/- 1.2. Prove the following lemmas. Notice that they are registered as simp rules thanks to the
`@[simp]` attribute. -/
@[simp] lemma drop_nil {α : Type} : ∀(n : ℕ), drop n ([] : list α) = [] :=
begin
intros n,
induction n,
simp,
refl,
simp[drop]
end


@[simp] lemma take_nil {α : Type} : ∀(n : ℕ), take n ([] : list α) = []:=
begin
intros n,
induction n,
simp,
refl,
simp[take]
end

/- 1.3. Follow the recursion pattern of `drop` and `take` to prove the following lemmas. In other
words, for each lemma, there should be three cases, and the third case will need to invoke the
induction hypothesis.

The first case is shown for `drop_drop`. Beware of the fact that there are three variables in the
`drop_drop` lemma (but only two arguments to `drop`). Hint: The `refl` tactic might be useful in the
third case of `drop_drop`.
-/

lemma drop_drop {α : Type} : ∀(m n : ℕ) (xs : list α), drop n (drop m xs) = drop (n + m) xs
| 0       n xs        := by refl
| (_ + 1) n []        := by simp
| (m + 1) n (x :: xs)       :=
begin
rw[<-add_assoc n m 1],
unfold drop,
simp[drop_drop m],
end


lemma take_take {α : Type} : ∀(m : ℕ) (xs : list α), take m (take m xs) = take m xs
| 0 m                    := by refl
| (_ + 1) m              := 
begin
induction m,
refl,
simp[take, take_take]
end

lemma take_drop {α : Type} : ∀(n : ℕ) (xs : list α), take n xs ++ drop n xs = xs
| 0 xs := by simp[take, drop]
| (_ + 1) xs :=
begin
induction xs,
simp[take_drop],
unfold take,
unfold drop,
rw[<-xs_ih],
simp,
rw[xs_ih],
simp[take_drop]
end



/- Question 2: Gauss's summation formula -/

/-- `sum_upto f n = f 0 + f 1 + ... + f n` -/
def sum_upto (f : ℕ → ℕ) : ℕ → ℕ
| 0       := f 0
| (m + 1) := sum_upto m + f (m + 1)

/- 2.1. Prove the following lemma, discovered by Carl Friedrich Gauss as a pupil.

Hints: The `ac_refl` tactic might be useful to reason about multiplication. The rules about `add`
and `mul` in `12_exercise.lean` exist with the same names about '+' and '*' in Lean's libraries. -/

lemma sum_upto_eq : ∀m : ℕ, 2 * sum_upto id m = m * (m + 1) 
| 0 := by refl
| (m + 1) :=
begin 
simp[mul_add, mul_comm],
rw[<-mul_comm m],
simp[sum_upto],
simp[mul_add],
simp[sum_upto_eq],
simp[mul_add],
simp[mul_comm]
end

/- 2.2. Prove the following property of `sum_upto`. -/

lemma sum_upto_mul (a : ℕ) (f : ℕ → ℕ) : ∀(n : ℕ), sum_upto (λi, a * f i) n = a * sum_upto f n 
| 0 := by refl
| (m + 1) :=
begin
simp[sum_upto],
simp[sum_upto_mul],
simp[mul_add]
end