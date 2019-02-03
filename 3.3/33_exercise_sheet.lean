/- Exercise 3.3: Programming Semantics — Denotational Semantics -/

/- First we repeat some material from the lecture. -/

import .x33_library

set_option pp.beta true

class complete_lattice (α : Type) extends partial_order α :=
(Inf    : set α → α)
(Inf_le : ∀{s a}, a ∈ s → Inf s ≤ a)
(le_Inf : ∀{s a}, (∀a', a' ∈ s → a ≤ a') → a ≤ Inf s)

namespace set

lemma ext {α : Type} {s t : set α} (h : ∀a, a ∈ s ↔ a ∈ t) : s = t :=
by funext a; exact propext (h a)

instance (α : Type) : complete_lattice (set α) :=
{ le          := (⊆),
  le_refl     := assume s a, id,
  le_trans    := assume s t u hst htu a has, htu $ hst $ has,
  le_antisymm := assume s t hst hts, ext $ assume a, ⟨assume h, hst h, assume h, hts h⟩,
  Inf         := assume f, {a | ∀s, s ∈ f → a ∈ s},
  Inf_le      := assume f s hsf a h, h _ hsf,
  le_Inf      := assume f s h a has t htf, h t htf has }

end set

def monotone {α β} [partial_order α] [partial_order β] (f : α → β) :=
∀a₁ a₂, a₁ ≤ a₂ → f a₁ ≤ f a₂

namespace monotone

lemma id {α : Type} [partial_order α] : monotone (λa : α, a) :=
assume a₁ a₂ ha, ha

lemma const {α β : Type} [partial_order α] [partial_order β] (b : β) : monotone (λa : α, b) :=
assume a₁ a₂ ha, le_refl b

lemma union {α β : Type} [partial_order α] (f g : α → set β)
  (hf : monotone f) (hg : monotone g) : monotone (λa, f a ∪ g a) :=
begin
  intros a b asmalb,
  intros bs fg,
  cases fg,
  apply or.intro_left,
  apply hf a,
  repeat{assumption},
  apply or.intro_right,
  apply hg a,
  repeat{assumption}
end

end monotone

namespace complete_lattice

variables {α : Type} [complete_lattice α]

def lfp (f : α → α) : α := Inf {x | f x ≤ x}

lemma lfp_le (f : α → α) (a : α) (h : f a ≤ a) : lfp f ≤ a := sorry
lemma le_lfp (f : α → α) (a : α) (h : ∀a', f a' ≤ a' → a ≤ a') : a ≤ lfp f := sorry
lemma lfp_eq (f : α → α) (hf : monotone f) : lfp f = f (lfp f) := sorry

end complete_lattice

open complete_lattice

def Id (α : Type) : set (α × α) := {x | x.2 = x.1 }

@[simp] lemma mem_Id {α : Type} (a b : α) :
  (a, b) ∈ Id α ↔ b = a :=
iff.rfl

def comp {α : Type} (r₁ r₂ : set (α × α)) : set (α × α) :=
{ x | ∃m, (x.1, m) ∈ r₁ ∧ (m, x.2) ∈ r₂ }

infixl ` ◯ ` : 90 := comp

@[simp] lemma mem_comp {α : Type} (r₁ r₂ : set (α × α)) (a b : α) :
  (a, b) ∈ r₁ ◯ r₂ ↔ (∃c, (a, c) ∈ r₁ ∧ (c, b) ∈ r₂) :=
iff.rfl

def restrict {α : Type} (r : set (α × α)) (p : α → Prop) : set (α × α) :=
{ x | p x.1 ∧ x ∈ r }

infixl ` ⇃ ` : 90 := restrict

@[simp] lemma mem_restrict {α : Type} (r : set (α × α)) (p : α → Prop) (a b : α) :
  (a, b) ∈ r ⇃ p ↔ p a ∧ (a, b) ∈ r :=
by refl


/- Question 1: Monotonicity -/

/- Prove the following two lemmas from the lecture. -/

lemma monotone_comp {α β : Type} [partial_order α] (f g : α → set (β × β))
  (hf : monotone f) (hg : monotone g) : monotone (λa, f a ◯ g a) :=
  begin
   intros a b asmalb h hp,
   cases hp,
   cases hp_h,
   simp[comp],
   apply exists.intro hp_w,
   apply and.intro,
   apply hf a,
   repeat{assumption},
   apply hg a,
   repeat{assumption}
  end



lemma monotone_restrict {α β : Type} [partial_order α] (f : α → set (β × β)) (p : β → Prop)
  (hf : monotone f) : monotone (λa, f a ⇃ p) :=
  begin
    intros a b asmalb h hp,
    simp[restrict],
    apply and.intro,
    cases hp,
    assumption,
    cases hp,
    apply hf a,
    repeat{assumption}
  end


/- Question 2: Kleene's theorem -/

/- We can compute the fixpoint by iteration by taking the union of all finite iterations of `f`:

    lfp f = ⋃n, f^^[n] ∅

where

    f^^[n] = f ∘ ⋯ ∘ f ∘ id

iterates the function `f` `n` times. However, the above characterization of `lfp` only holds for
continuous functions, a concept we will introduce below. -/

def iterate {α : Type} (f : α → α) : ℕ → α → α
| 0       a := a
| (n + 1) a := f (iterate n a)

notation f`^^[`n`]` := iterate f n

/- 2.1. Fill in the missing proofs below. -/

def Union {α : Type} (s : ℕ → set α) : set α :=
{ a | ∃n, a ∈ s n }

lemma Union_le {α : Type} {s : ℕ → set α} (a : set α) (h : ∀i, s i ≤ a) : Union s ≤ a :=
begin
  intro u,
  intro us,
  cases us,
  apply h us_w,
  assumption
end

/- A continuous function `f` is a function that commutes with the union of any monotone sequence
`s`: -/

def continuous {α : Type} (f : set α → set α) : Prop :=
∀s : ℕ → set α, monotone s → f (Union s) = Union (λn, f (s n))

/- We need to prove that each continuous function is monotone. To achieve this, we will need the
following sequence: -/

def bi_seq {α : Type} (a₁ a₂ : set α) : ℕ → set α
| 0       := a₁
| (n + 1) := a₂

/- For example, `bi_seq 0 1` is the sequence 0, 1, 1, 1, etc. -/

lemma monotone_bi_seq {α : Type} (a₁ a₂ : set α) (h : a₁ ≤ a₂) :
  monotone (bi_seq a₁ a₂)
| 0       0       _ := le_refl _
| 0       (n + 1) _ := h
| (n + 1) (m + 1) _ := le_refl _

lemma Union_bi_seq {α : Type} (a₁ a₂ : set α) (ha : a₁ ≤ a₂) :
  Union (bi_seq a₁ a₂) = a₂ :=
begin
  apply le_antisymm,
  apply Union_le,
  intro i,
  intros a b,
  cases i,
  apply ha b,
  exact b,
  intros a1 a2,
  apply exists.intro 
end

lemma monotone_of_continuous {α : Type} (f : set α → set α) (hf : continuous f) :
  monotone f :=
begin
intros a1 a2,
intros smaller,
apply Union_bi_seq,
 
end

/- 2.2. Provide the following proof, using a similar case distinction as for `monotone_bi_seq`
above. -/

lemma monotone_iterate {α : Type} (f : set α → set α) (hf : monotone f) :
  monotone (λn, f^^[n] ∅)
:= sorry

/- 2.3. Prove the main theorem. A proof sketch is given below.

We break the proof into two proofs of inclusion.

Case 1. lfp f ≤ Union (λn, f^[n] ∅): The key is to use the lemma `lfp_le` together with continuity
of `f`.

Case 2. Union (λn, f^[n] ∅) ≤ lfp f: The lemma `Union_le` gives us a natural number `i`, on which
you can perform induction. You will also need the lemma `lfp_eq` to unfold one iteration of
`lfp f`. -/

lemma lfp_Kleene {α : Type} (f : set α → set α) (hf : continuous f) :
  lfp f = Union (λn, f^^[n] ∅) :=
be


/- Question 3 **optional**: Regular expressions -/

inductive regex (α : Type) : Type
| empty     {} : regex
| nothing   {} : regex
| atom (a : α) : regex
| concat       : regex → regex → regex
| alt          : regex → regex → regex
| star         : regex → regex

open regex

/- 3.1 **optional**. Define a translation of regular expressions to relations. The idea is that an
atom corresponds to a relation, concatenation corresponds to composition of relations, and
alternation is union. -/

def rel_of_regex {α : Type} : regex (set (α × α)) → set (α × α)
| empty          := Id α
| _              := sorry

/- 3.2 **optional**. Prove the following recursive equation about your definition. -/

lemma rel_of_regex_star {α : Type} (r : regex (set (α × α))) :
  rel_of_regex (star r) = rel_of_regex (alt (concat r (star r)) empty) :=
sorry
