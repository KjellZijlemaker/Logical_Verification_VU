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
    { cases h with n' h,
      exact exists_minimal_arg.aux _ n' rfl },
    { have h' : ∀n', x ≤ f n',
      { intro n',
        apply le_of_not_gt _,
        intro h',
        exact h ⟨n', h'⟩ },
      apply exists.intro n,
      rw eq,
      exact h' }
  end

/- Now this interesting lemma falls off: -/

lemma exists_minimal_arg (f : ℕ → ℕ) : ∃n : ℕ, ∀i : ℕ, f n ≤ f i :=
exists_minimal_arg.aux f _ 0 rfl

/- 1.2. Use what you learned in the lecture notes to define the following function, which returns
the (or an) index of the minimal element in `f`'s image. -/

noncomputable def minimal_arg (f : ℕ → ℕ) : ℕ :=
classical.some (exists_minimal_arg f)

/- 1.3. Prove the following characteristic lemma about your definition. -/

lemma minimal_arg_spec (f : ℕ → ℕ) : ∀i : ℕ, f (minimal_arg f) ≤ f i :=
classical.some_spec (exists_minimal_arg f)


/- Question 2: Integers as quotients -/

/- First, we repeat some material from the lecture. As usual, ignore the `sorry`. -/

namespace exercise


lemma reflexive1 {α: Type} (x: (ℕ × ℕ)) : x.1 + x.2 = x.1 + x.2:= by refl
lemma symmetry1 {α: Type} (x y: (ℕ × ℕ)) (h1: x.1 + y.2 = y.1 + x.2) :  y.1 + x.2 = x.1 + y.2 := by rw[h1]
lemma transitive1 {α: Type} (x y z: (ℕ × ℕ)) (h1: y.1 + x.2 = x.1 + y.2) (h2:  z.1 + y.2 = y.1 + z.2) : (x.1 + z.2) + y.2 = (x.1 + y.2) + z.2 := begin calc (x.fst + z.snd) + y.snd = (x.fst + y.snd) + z.snd : by ac_refl  end 


lemma reflexivelist {α: Type} (xs: list α) : ∀x, x∈xs ↔ x∈xs := begin intro x, apply iff.intro, intro h, assumption, intro h, assumption end
lemma symmetriclist {α: Type} (xs ys: list α) : ∀x, x∈xs ↔ x∈ys →  x∈ys ↔ x∈xs := begin intro x, apply iff.intro, intro h, cases h, apply h_mpr, intro s, assumption, intro h, apply iff.intro, intros a b, assumption, intro a, assumption end
lemma transitivelist {α: Type} (xs ys zs: list α) : ∀x, x∈xs ↔ x∈ys →  x∈ys ↔ x∈zs → x ∈xs ↔ x∈zs := begin intro x, apply iff.intro, intro h, cases h, simp[symmetriclist] at h_mp, simp[symmetriclist] at h_mpr, sorry  


instance fin_set.rel (α: Type) : setoid (list α) :={ r :=λxs ys,∀x, x∈xs↔x∈ys,
iseqv := ⟨ (assume xs, by simp*),

 ⟩ }

instance int.rel : setoid (ℕ × ℕ) :=
{ r     := λa b, a.1 + b.2 = b.1 + a.2,
  iseqv := ⟨ (assume a, reflexive1 ),
            (assume a b eq, symmetry1),
            (assume a b c d e , transitive1)
  ⟩ }

@[simp] lemma rel_iff (a b : ℕ × ℕ) : a ≈ b ↔ a.1 + b.2 = b.1 + a.2 := iff.rfl

def int : Type := quotient int.rel

/- 2.1. Define negation using `quotient.lift_on`. -/

def neg (a : int) : int :=
quotient.lift_on a (λpn, ⟦(pn.2, pn.1)⟧)
  begin
    intros a b h,
    cases a,
    cases b,
    apply quotient.sound,
    simp at h ⊢,
    rw [h]
  end

/- 2.2. Prove the following lemmas. -/

lemma neg_mk (p n : ℕ) : neg ⟦(p, n)⟧ = ⟦(n, p)⟧ :=
by refl

lemma neg_neg (a : int) : neg (neg a) = a :=
begin
  refine quotient.induction_on a _,
  intro a,
  cases a,
  simp [neg_mk]
end

end exercise
