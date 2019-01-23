/- Lecture 4.1: Mathematics — Foundation -/

namespace lecture


/- Type universes -/

#check (Prop   : Type)
#check (Type   : Type 1)
#check (Type 1 : Type 2)
#check (Type 2 : Type 3)

-- declare universe names
universes u v

example : Prop   = Sort 0       := by refl
example : Type   = Sort 1       := by refl
example : Type   = Type 0       := by refl
example : Type u = Sort (u + 1) := by refl

#check (Type u : Type (u + 1))

-- `ulift α` is isomorphic to `α`
#check ulift.{u v}
#check @ulift.up.{u v}
#check @ulift.down.{u v}

#check plift.{0}


/- `Prop` vs. `Type` -/

-- `Prop` is a subsingleton
example {p : Prop} {h₁ h₂ : p} : h₁ = h₂ := by refl


/- Large elimination -/

#check @false.elim        -- in a contradictory context
#check @and.rec
#check @eq.rec            -- substitution in `Prop` and `Type`
#check @well_founded.rec  -- induction or well-founded recursion


/- The axiom of choice -/

#print classical.choice

#check classical.some
#check classical.some_spec
#check classical.em
#check classical.prop_decidable


/- Quotient types -/

set_option pp.beta true

-- `quot` for arbitrary relations
#print quot
#print quot.mk
#print quot.lift
#print quot.sound

-- `quotient` for equivalence relations
#print quotient
#print setoid
#check quotient.lift_on
#check quotient.lift_on₂
#check quotient.exact

#check (≈)


/- Integers as a quotient -/

/- Basic idea: `(p, n)` represents `p - n` -/

instance int.rel : setoid (ℕ × ℕ) :=
{ r     := λa b, a.1 + b.2 = b.1 + a.2,
  iseqv :=
  ⟨ (assume a, rfl),
    (assume a b eq, eq.symm),
    (assume a b c eq_ab eq_bc,
      have (a.1 + c.2) + b.2 = (c.1 + a.2) + b.2 :=
        calc (a.1 + c.2) + b.2 = (a.1 + b.2) + c.2 : by ac_refl
        ... = a.2 + (b.1 + c.2) : by rw [eq_ab]; ac_refl
        ... = (c.1 + a.2) + b.2 : by rw [eq_bc]; ac_refl,
      calc a.1 + c.2 = c.1 + a.2 : eq_of_add_eq_add_right this) ⟩ }

@[simp] lemma rel_iff (a b : ℕ × ℕ) : a ≈ b ↔ a.1 + b.2 = b.1 + a.2 :=
iff.rfl

def int : Type := quotient int.rel

def zero : int := ⟦(0, 0)⟧

example (n : ℕ) : zero = ⟦(n, n)⟧ :=
begin
  unfold zero,
  apply quotient.sound,
  rw [rel_iff],
  simp
end

def add (a b : int) : int :=
quotient.lift_on₂ a b (λa b, ⟦(a.1 + b.1, a.2 + b.2)⟧)
  begin
    intros a₁ b₁ a₂ b₂ ha hb,
    apply quotient.sound,
    simp only [rel_iff] at ha hb ⊢,
    calc  (a₁.1 + b₁.1) + (a₂.2 + b₂.2) =
          (a₁.1 + a₂.2) + (b₁.1 + b₂.2) : by ac_refl
    ... = (a₂.1 + a₁.2) + (b₂.1 + b₁.2) : by rw [ha, hb]
    ... = (a₂.1 + b₂.1) + (a₁.2 + b₁.2) : by ac_refl
  end

lemma add_mk (ap an bp bn : ℕ) : add ⟦(ap, an)⟧ ⟦(bp, bn)⟧ = ⟦(ap + bp, an + bn)⟧ :=
by refl

lemma add_zero (i : int) : add zero i = i :=
quotient.induction_on i
  begin
    intro p,
    cases p,
    simp [zero, add_mk]
  end

end lecture
