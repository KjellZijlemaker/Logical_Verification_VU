/- Lecture 1.2: Basics — Proofs -/

/- Computation -/

-- β-reduction (reduce λ-abstraction + application)
example {α β : Type} (f : α → β) (a : α) :
  (λx, f x) a = f a :=
by refl

-- δ-reduction (unfold definition)
section

def f (n : ℕ) : ℕ := n + n

example (m : ℕ) : f m = m + m :=
by refl

end

-- ι-reduction (projection)
example {α β : Type} (a : α) (b : β) :
  prod.fst (a, b) = a :=
by refl

-- ζ-reduction (`let`-unfolding)
example : (let x : ℕ := 2 in 2 + 2) = 4 :=
by refl

-- η-reduction
example {α β : Type} (f : α → β) : (λx, f x) = f :=
by refl

/- Natural numbers -/

namespace my_nat

def add : nat → nat → nat
| m 0            := m
| m (nat.succ n) := nat.succ (add m n)

/- Commutativity of `add` -/

lemma add_zero : ∀n : ℕ, add 0 n = n
| 0            := by refl
| (nat.succ m) := by simp [add, add_zero m]

example (n : ℕ) : add 0 n = n :=
begin
  induction n,
  { refl },
  { simp [add, n_ih] }
end

example (n : ℕ) : add 0 n = n :=
by induction n; simp [add, *]

lemma add_succ : ∀m n : ℕ, add (nat.succ m) n = nat.succ (add m n)
| m 0            := by refl
| m (nat.succ n) := by simp [add, add_succ m n]

lemma add_comm : ∀m n : ℕ, add m n = add n m
| m 0            := by simp [add, add_zero]
| m (nat.succ n) := by simp [add, add_succ, add_comm m n]

example : ∀m n : ℕ, add m n = add n m
| m 0            := by simp [add, add_zero]
| m (nat.succ n) :=
  have add_succ : ∀m n : ℕ, add (nat.succ m) n = nat.succ (add m n) :=
    by intros m n; induction n; simp [add, *],
  by simp [add, add_succ, add_comm m n]

example : ∀m n : ℕ, add m n = add n m
| m 0            := by simp [add, add_zero]
| m (nat.succ n) :=
  have ih : _ := add_comm m n,
  by simp [add, add_succ, ih]

/- Associativity of `add` -/

lemma add_assoc : ∀l m n : ℕ, add (add l m) n = add l (add m n)
| l m 0            := by refl
| l m (nat.succ n) := by simp [add, add_assoc l m n]

instance : is_commutative ℕ add := ⟨add_comm⟩
instance : is_associative ℕ add := ⟨add_assoc⟩

def mul : ℕ → ℕ → ℕ
| _ 0            := 0
| m (nat.succ n) := add m (mul m n)

/- Distributivity -/

lemma mul_add (l m : ℕ) : ∀n : ℕ, mul l (add m n) = add (mul l m) (mul l n)
| 0            := by refl
| (nat.succ l) := begin simp [add, mul, mul_add l], ac_refl end

end my_nat


/- Lists -/

def reverse {α : Type} : list α → list α
| []        := []
| (x :: xs) := reverse xs ++ [x]

/- `reverse` of `reverse` is identity -/
lemma reverse_append {α : Type} :
  ∀xs ys : list α, reverse (xs ++ ys) = reverse ys ++ reverse xs
| [] ys := by simp[reverse]
| (x :: xs) ys := begin simp[reverse, reverse_append] end



lemma reverse_reverse {α : Type} : ∀xs : list α, reverse (reverse xs) = xs
| [] := by simp[reverse]
| (x :: xs) := begin simp[reverse], simp[reverse_append], rw[reverse_reverse], rw[reverse], rw[reverse], refl  end

def map {α : Type} {β : Type} (f : α → β) : list α → list β
| [] := []
| (x :: xs) :=  f x :: map xs


-- lemma reverse_append {α : Type} :
--   ∀xs ys : list α, reverse (xs ++ ys) = reverse ys ++ reverse xs
-- | []        ys := by simp [reverse]
-- | (x :: xs) ys := begin simp [reverse, reverse_append xs] end

-- lemma reverse_reverse {α : Type} : ∀xs : list α, reverse (reverse xs) = xs
-- | []        := by refl
-- | (x :: xs) := by simp [reverse, reverse_append, reverse_reverse xs]

-- def map {α : Type} {β : Type} (f : α → β) : list α → list β
-- | []        := []
-- | (x :: xs) := f x :: map xs

/- Functorial properties of `map` -/

lemma map_ident {α : Type} : ∀xs : list α, map (λx, x) xs = xs
| []        := by refl
| (x :: xs) := begin rw[map],  end

example {α : Type} : ∀xs : list α, map (λx, x) xs = xs
| []        := by refl
| (x :: xs) :=
  have ih : map (λx, x) xs = xs := _example xs,
  begin rw map, rw ih end

example {α : Type} : ∀xs : list α, xs = map (λx, x) xs
| []        := by refl
| (x :: xs) :=
  have ih : _ := _example xs,
  begin rw [map, ←ih] end

lemma map_comp {α β γ : Type} (f : α → β) (g : β → γ) :
  ∀xs : list α, map (λx, g (f x)) xs = map g (map f xs)
| []        := by refl
| (x :: xs) := begin rw[map], rw[map_comp], rw[map], rw[map] end

lemma map_append {α β : Type} (f : α → β) :
  ∀xs ys : list α, map f (xs ++ ys) = map f xs ++ map f ys
| []        ys := by refl
| (x :: xs) ys := begin rw[map], rw[map_append], end

lemma map_reverse {α β : Type} (f : α → β) :
  ∀xs : list α, map f (reverse xs) = reverse (map f xs)
| []        := by refl
| (x :: xs) := by simp [map, reverse, map_append, map_reverse xs]


/- RGB values -/

structure rgb :=
(red green blue : ℕ)

def shuffle (c : rgb) : rgb :=
{red := c.green, green := c.blue, blue := c.red}

lemma shuffle_shuffle_shuffle (c : rgb) : shuffle (shuffle (shuffle c)) = c :=
by cases c; refl

example (c : rgb) : shuffle (shuffle (shuffle c)) = c :=
begin cases c, refl end

example : ∀c : rgb, shuffle (shuffle (shuffle c)) = c
| ⟨_, _, _⟩ := by refl
