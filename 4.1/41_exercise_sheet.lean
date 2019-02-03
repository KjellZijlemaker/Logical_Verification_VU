/- Exercise 4.1: Mathematics — Foundation -/

/- Question 1: Hilbert choice -/

/- The following command enables noncomputable decidability on every `Prop`. The `priority 0`
attribute ensures this is used only when necessary; otherwise, it would make some computable
definitions noncomputable for Lean. -/

local attribute [instance, priority 0] classical.prop_decidable

/- 1.1. Prove the following lemma. -/

lemma exists_minimal_arg.aux (f : ℕ → ℕ) :
  ∀x n, f n = x → ∃n, ∀i, f n ≤ f i
| x n eq :=
  begin
    -- this works thanks to `classical.prop_decidable`
    by_cases (∃n', f n' < x),
    cases h,
    apply exists_minimal_arg.aux _ h_w _,
    apply x,
    apply le_e
    cases eq,
    
    
  end

/- Now this interesting lemma falls off: -/

lemma exists_minimal_arg (f : ℕ → ℕ) : ∃n : ℕ, ∀i : ℕ, f n ≤ f i :=
exists_minimal_arg.aux f _ 0 rfl

/- 1.2. Use what you learned in the lecture notes to define the following function, which returns
the (or an) index of the minimal element in `f`'s image. -/

noncomputable def minimal_arg (f : ℕ → ℕ) : ℕ :=
sorry

/- 1.3. Prove the following characteristic lemma about your definition. -/

lemma minimal_arg_spec (f : ℕ → ℕ) : ∀i : ℕ, f (minimal_arg f) ≤ f i :=
sorry


/- Question 2: Integers as quotients -/

/- First, we repeat some material from the lecture. As usual, ignore the `sorry`. -/

namespace exercise

instance int.rel : setoid (ℕ × ℕ) :=
{ r     := λa b, a.1 + b.2 = b.1 + a.2,
  iseqv :=
  ⟨ (assume a, rfl),
    (assume a b eq, eq.symm),
    (assume a b c fst snd, 
    have (a.fst + c.snd) + b.snd = (c.fst + a.snd) + b.snd := 
    calc (a.fst + c.snd) + b.snd = (a.fst + b.snd) + c.snd    : by ac_refl
                             ... =  a.snd + (b.fst + c.snd)   : by {rw[fst], ac_refl}
                             ... =  (c.fst + a.snd ) + b.snd  : by {rw[snd], ac_refl},
    calc (a.fst + c.snd) = (c.fst + a.snd)                    : by {apply eq_of_add_eq_add_right this})⟩ 
    }


def count {α: Type} (a: α) [decidable_eq α]: list α → ℕ
| [] := 0
| (x :: xs) := if x = a then 1 + count xs else count xs

#reduce count 2[2,2,2,2]


  instance list.rel (α: Type) : setoid (list α) :=
{ r     := λxs ys, ∀x, count x xs = count x ys,
  iseqv := 
  ⟨ (assume xs, begin simp end),
  (assume xs ys a b c, begin simp *, end)
  (assume xs ys zs xs_zs ys_zs, by simp *) ⟩ }

lemma rel_set {α: Type} (xs ys: list α): xs ≈ ys ↔ count xs = count ys := sorry


def multiset (α: Type): Type := quotient (list.rel α)

-- lemma counter {α: Type} (xs xs_ys ys ys_xs: list α): count (xs ++ ys) = count xs + count ys

lemma r_reflexive {α: Type} (xs : list α) : r count xs xs 
lemma r_symmetric (xs ys : list α) : r xs ys → r ys xs 
lemma r_transitive (xs ys zs : listα) : r xs ys→r ys zs→r xs zs

def empty_mset {α: Type}: multiset α :=  ⟦[]⟧ 
def singleton_mset {α: Type} (a: α) : multiset α :=  ⟦[a]⟧
def sum_mset {α: Type} (A: multiset α) (B: multiset α) : multiset α :=
quotient.lift_on₂ A B (λxs ys, ⟦xs ++ ys⟧ )
begin 
intros xs ys xs_ys ys_xs,
intro xs1,
intro ys1,
apply quotient.sound,
simp[rel_set],
simp[rel_set] at xs1,
simp[rel_set] at ys1,

end


inductive finite {α: Type}: set α → Prop
|empty : finite ∅
|singleton (a: α) : finite({a})
|union (A B: set α) (h: finite A) (s: finite B) : finite(A ∪ B)

def multiset2 (α: Type) : Type := subtype (finite α)

@[simp] lemma rel_iff (a b : ℕ × ℕ) : a ≈ b ↔ a.1 + b.2 = b.1 + a.2 := iff.rfl

def int : Type := quotient int.rel

/- 2.1. Define negation using `quotient.lift_on`. -/

def neg (a : int) : int :=
quotient.lift_on a (λpn, ⟦(pn.2, pn.1)⟧ )
begin
intros pn b pnb,
simp[rel_iff],
apply quotient.sound,
simp,
simp at pnb,
rw[pnb]
end

/- 2.2. Prove the following lemmas. -/

lemma neg_mk (p n : ℕ) : neg ⟦(p, n)⟧ = ⟦(n, p)⟧:=
begin
unfold neg,
apply quotient.sound,
rw[rel_iff]
end

lemma neg_neg (a : int) : neg (neg a) = a :=
begin
apply quotient.induction_on a,
intro n,
cases n,
refl
end

end exercise
