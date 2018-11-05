/- Homework 1.2: Basics — Proofs -/

/- Question 1: Drop and Take -/

def drop {α : Type} : ℕ → list α → list α
| 0       xs        := xs
| (_ + 1) []        := []
| (m + 1) (x :: xs) := drop m xs

/- 1.1. Define `take`. -/

/- To avoid bad surprises in the proofs, we recommend that you follow the same recursion pattern as
for `drop` above. -/

def take {α : Type} : ℕ → list α → list α
:= sorry

#reduce take 0 [3, 7, 11]   -- expected: []
#reduce take 1 [3, 7, 11]   -- expected: [3]
#reduce take 2 [3, 7, 11]   -- expected: [3, 7]
#reduce take 3 [3, 7, 11]   -- expected: [3, 7, 11]
#reduce take 4 [3, 7, 11]   -- expected: [3, 7, 11]

-- when `#reduce` fails for some obscure reason, try `#eval`:
#eval take 2 ["a", "b", "c"]   -- expected: ["a", "b"]

/- 1.2. Prove the following lemmas. Notice that they are registered as simp rules thanks to the
`@[simp]` attribute. -/

@[simp] lemma drop_nil {α : Type} : ∀(n : ℕ), drop n ([] : list α) = []
:= sorry

@[simp] lemma take_nil {α : Type} : ∀(n : ℕ), take n ([] : list α) = []
:= sorry

/- 1.3. Follow the recursion pattern of `drop` and `take` to prove the following lemmas. In other
words, for each lemma, there should be three cases, and the third case will need to invoke the
induction hypothesis.

The first case is shown for `drop_drop`. Beware of the fact that there are three variables in the
`drop_drop` lemma (but only two arguments to `drop`). Hint: The `refl` tactic might be useful in the
third case of `drop_drop`.
-/

lemma drop_drop {α : Type} : ∀(m n : ℕ) (xs : list α), drop n (drop m xs) = drop (n + m) xs
| 0       n xs        := by refl
-- add the two missing cases here

lemma take_take {α : Type} : ∀(m : ℕ) (xs : list α), take m (take m xs) = take m xs
:= sorry

lemma take_drop {α : Type} : ∀(n : ℕ) (xs : list α), take n xs ++ drop n xs = xs
:= sorry


/- Question 2: Gauss's summation formula -/

/-- `sum_upto f n = f 0 + f 1 + ... + f n` -/
def sum_upto (f : ℕ → ℕ) : ℕ → ℕ
| 0       := f 0
| (m + 1) := sum_upto m + f (m + 1)

/- 2.1. Prove the following lemma, discovered by Carl Friedrich Gauss as a pupil.

Hints: The `ac_refl` tactic might be useful to reason about multiplication. The rules about `add`
and `mul` in `12_exercise.lean` exist with the same names about '+' and '*' in Lean's libraries. -/

lemma sum_upto_eq : ∀m : ℕ, 2 * sum_upto id m = m * (m + 1)
:= sorry

/- 2.2. Prove the following property of `sum_upto`. -/

lemma sum_upto_mul (a : ℕ) (f : ℕ → ℕ) : ∀(n : ℕ), sum_upto (λi, a * f i) n = a * sum_upto f n
:= sorry
