/- Exercise 1.2: Basics — Proofs -/

/- Question 1: Natural numbers -/

namespace my_nat

def add : ℕ → ℕ → ℕ
| 0            n := n
| (nat.succ m) n := nat.succ (add m n)


-- def add : nat → nat → nat
-- | m nat.zero     := m
-- | m (nat.succ n) := nat.succ (add m n)



-- lemma natzero (m : nat) : add m 0 = m:=
-- begin
-- induction m,
-- simp[add],
-- refl
-- end


-- lemma test (m : nat) :  add 0 m = m:=
-- begin
-- induction m,
-- refl,
-- simp[add]

-- end


-- lemma add_commm (m n : nat) : add m n = add n m :=
-- begin
-- induction m,
-- simp[natzero, add],



-- end

/- We proved these properties already in the lecture, so we take them as axioms here. (We will often
use `sorry` like this to avoid clutter in exercise sheets. But keep in mind that `sorry` is a risky
construct.) -/

lemma add_zero : ∀m : ℕ, add m 0 = m
| (nat.succ m) := by simp [add, add_zero m]
| 0            := by refl


lemma add_succ : ∀m n : ℕ, add m (nat.succ n) = nat.succ (add m n)
| m 0 := by refl

lemma add_comm : ∀m n : ℕ, add m n = add n m := sorry
lemma add_assoc : ∀l m n : ℕ, add (add l m) n = add l (add m n) := sorry

instance : is_commutative ℕ add := ⟨add_comm⟩
instance : is_associative ℕ add := ⟨add_assoc⟩

def mul : ℕ → ℕ → ℕ
| 0            _ := 0
| (nat.succ m) n := add n (mul m n)

lemma mul_add (m n : ℕ) : ∀l : ℕ, mul (add l m) n = add (mul l n) (mul m n) := sorry

/- 1.1. Prove the following recursive equations on the second argument of `mul`. -/

lemma mul_zero : ∀m : ℕ, mul m 0 = 0
:= sorry

lemma mul_succ : ∀m n : ℕ, mul m (nat.succ n) = add (mul m n) m
:= sorry

/- 1.2. Prove commutativity and associativity of multiplication by induction. Choose the induction
variable carefully. Use the pattern matching syntax. -/

lemma mul_comm : ∀m n : ℕ, mul m n = mul n m
:= sorry

lemma mul_assoc : ∀l m n : ℕ, mul (mul l m) n = mul l (mul m n)
:= sorry

/- 1.3. Prove the same lemmas as in 1.2, but using the `induction` tactic instead. Try to reuse as
much of the above proof as possible. -/

example (m n : ℕ) : mul m n = mul n m :=
sorry

example : ∀l m n : ℕ, mul (mul l m) n = mul l (mul m n) :=
sorry

/- 1.4. Prove the symmetric variant of `mul_add` using `rw`. To apply commutativity at a specific
position instantiate the rule (e.g. `mul_comm n`). -/

lemma add_mul (m n l : ℕ) : mul n (add l m) = add (mul n l) (mul n m) :=
sorry

end my_nat


/- Question 2: Lists -/

def reverse {α : Type} : list α → list α
| []        := []
| (x :: xs) := reverse xs ++ [x]

/- Another pesky `sorry`. -/
lemma reverse_reverse {α : Type} (xs : list α) : reverse (reverse xs) = xs := sorry

/- We define a new accumulator-based version of `reverse`. The first argument serves as the
accumulator. This definition is *tail-recursive*, meaning that compilers and interpreters can easily
optimize the recursion away, resulting in more efficient code. -/

def areverse {α : Type} : list α → list α → list α
| ys []        := ys
| ys (x :: xs) := areverse (x :: ys) xs

/- 2.1. Our intention is that `areverse [] xs` should be equal to `reverse xs`. But if we start an
induction, we quickly see that the induction hypothesis is not strong enough. Start by proving the
following generalization (using pattern matching or the `induction` tactic): -/

-- lemma areverse_eq_reverse_append {α : Type} : ∀ys xs : list α, areverse ys xs = reverse xs ++ ys
-- | [] xs := begin simp[reverse], simp[areverse_eq_reverse] end

/- 2.2. Derive the desired equation. -/

lemma areverse_eq_reverse {α : Type} (xs : list α) : areverse [] xs = reverse xs:=
begin induction xs, simp[areverse], simp[reverse], simp[areverse], simp[reverse], rw[<-xs_ih],  end

/- 2.3. Prove the following property. Hint: A one-line inductionless proof is possible. -/

lemma areverse_areverse {α : Type} (xs : list α) : areverse [] (areverse [] xs) = xs :=
:= sorry
