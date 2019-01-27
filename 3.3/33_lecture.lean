/- Lecture 3.3: Programming Semantics — Denotational Semantics -/

import .x33_library

-- enables β-reduced output
set_option pp.beta true


/- Complete lattices -/

class complete_lattice (α : Type) extends partial_order α :=
(Inf    : set α → α)
(Inf_le : ∀{s a}, a ∈ s → Inf s ≤ a)
(le_Inf : ∀{s a}, (∀a', a' ∈ s → a ≤ a') → a ≤ Inf s)

notation `⨅` := complete_lattice.Inf


/- Instance for complete lattices: `set α` -/

namespace set

lemma ext {α : Type} {s t : set α} (h : ∀a, a ∈ s ↔ a ∈ t) : s = t :=
begin
  funext a,
  apply propext,
  exact (h a)
end

instance (α : Type) : complete_lattice (set α) :=
{ le          := (⊆),
  le_refl     := assume s a, id,
  le_trans    := assume s t u hst htu a has, htu $ hst $ has,
  le_antisymm := assume s t hst hts,
    begin
      apply ext,
      intro a,
      apply iff.intro,
      exact assume h, hst h,
      exact assume h, hts h
    end,
  Inf         := assume f, {a | ∀s, s ∈ f → a ∈ s},
  Inf_le      := assume f s hsf a h, begin simp at h, exact h s hsf end,
  le_Inf      := assume f s h a has t htf, h t htf has }

end set


/- Monotonicity of functions -/

def monotone {α β} [partial_order α] [partial_order β] (f : α → β) :=
∀a₁ a₂, a₁ ≤ a₂ → f a₁ ≤ f a₂

namespace monotone

lemma id {α : Type} [partial_order α] : monotone (λa : α, a) :=
assume a₁ a₂ ha, ha

lemma const {α β : Type} [partial_order α] [partial_order β] (b : β) : monotone (λa : α, b) :=
begin
intros a b c,
apply le_refl
end

lemma union {α β : Type} [partial_order α] (f g : α → set β) (hf : monotone f) (hg : monotone g) :
  monotone (λa, f a ∪ g a) :=
begin
  intros a₁ a₂ ha b hb,
  cases hb,
  { exact or.intro_left _ (hf a₁ a₂ ha hb) },
  { exact or.intro_right _ (hg a₁ a₂ ha hb) },
end

end monotone


/- Least fixpoint -/

namespace complete_lattice

variables {α : Type} [complete_lattice α]

def lfp (f : α → α) : α :=
⨅ {x | f x ≤ x}

lemma lfp_le (f : α → α) (a : α) (h : f a ≤ a) :
  lfp f ≤ a :=
Inf_le h

lemma le_lfp (f : α → α) (a : α) (h : ∀a', f a' ≤ a' → a ≤ a') :
  a ≤ lfp f :=
le_Inf h

lemma lfp_eq (f : α → α) (hf : monotone f) :
  lfp f = f (lfp f) :=
begin
  have h : f (lfp f) ≤ lfp f :=
  begin
    apply le_lfp,
    intros a' ha',
    apply @le_trans _ _ _ (f a'),
    { apply hf,
      apply lfp_le,
      assumption },
    { assumption }
  end,
  apply le_antisymm,
  { apply lfp_le,
    apply hf,
    assumption },
  { assumption }
end

end complete_lattice


/- Relations -/

namespace lecture

open complete_lattice

def Id (α : Type) : set (α × α) := { x | x.2 = x.1 }

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

/- We will prove the following two lemmas in the exercise. -/

lemma monotone_comp {α β : Type} [partial_order α] (f g : α → set (β × β))
  (hf : monotone f) (hg : monotone g) : monotone (λa, f a ◯ g a) :=
sorry

lemma monotone_restrict {α β : Type} [partial_order α] (f : α → set (β × β)) (p : β → Prop)
  (hf : monotone f) : monotone (λa, f a ⇃ p) :=
sorry


/- Denotational semantics -/

open program

variables {c : state → Prop} {f : state → ℕ} {p p₀ p₁ p₂ : program}

def den : program → set (state × state)
| skip          := Id state
| (assign n f)  := {x | x.2 = x.1.update n (f x.1)}
| (seq p₁ p₂)   := den p₁ ◯ den p₂
| (ite c p₁ p₂) := (den p₁ ⇃ c) ∪ (den p₂ ⇃ (λs, ¬ c s))
| (while c p)   := lfp (λW, ((den p ◯ W) ⇃ c) ∪ (Id state ⇃ λs, ¬ c s))

notation `⟦` p `⟧`:= den p

lemma den_while (p : program) (c : state → Prop) :
  ⟦ while c p ⟧ = ⟦ ite c (p ;; while c p) skip ⟧ :=
begin
  apply lfp_eq,
  apply monotone.union,
  { apply monotone_restrict,
    apply monotone_comp,
    { exact monotone.const _ },
    { exact monotone.id } },
  { exact monotone.const _ }
end


/- Equivalence of denotational and big-step semantics -/

lemma den_of_big_step (p : program) (s t : state) :
  (p, s) ⟹ t → (s, t) ∈ ⟦ p ⟧ :=
begin
  generalize eq : (p, s) = ps,
  intro h,
  induction h generalizing eq p s;
    cases eq;
    -- simplify only if the simplifier solves the goal completely
    try { simp [den, *], done },
  { exact ⟨h_t, h_ih_h₁ _ _ rfl, h_ih_h₂ _ _ rfl⟩ },
  { rw [den_while, den],
    simp [*],
    exact ⟨h_t, h_ih_hp _ _ rfl, h_ih_hw _ _ rfl⟩ },
  { rw [den_while],
    simp [den, *] }
end

lemma big_step_of_den :
  ∀(p : program) (s t : state), (s, t) ∈ ⟦ p ⟧ → (p, s) ⟹ t
| skip s t          :=
  by simp [den] {contextual := tt}; exact _
| (assign n f) s t  :=
  by simp [den] {contextual := tt}
| (seq p₁ p₂) s t   :=
  begin
    assume h,
    cases h with u hu,
    exact big_step.seq u (big_step_of_den p₁ _ _ hu.left) (big_step_of_den p₂ _ _ hu.right)
  end
| (ite c p₁ p₂) s t :=
  assume h,
  match h with
  | or.intro_left  _ ⟨hs, hst⟩ := big_step.ite_true  hs (big_step_of_den p₁ _ _ hst)
  | or.intro_right _ ⟨hs, hst⟩ := big_step.ite_false hs (big_step_of_den p₂ _ _ hst)
  end
| (while c p) s t   :=
  begin
    have hw : ⟦while c p⟧ ≤ {x | (while c p, x.1) ⟹ x.2},
    { apply lfp_le _ _ _,
      intros x hx,
      cases x with s t,
      simp at hx,
      cases hx,
      { cases hx with hs hst,
        cases hst with u hu,
        apply big_step.while_true u hs,
        { exact big_step_of_den p _ _ hu.left },
        { exact hu.right } },
      { cases hx,
        cases hx_right,
        apply big_step.while_false hx_left } },
    exact assume h, hw h
  end

lemma den_eq_bigstep (p : program) (s t : state ) : (s, t) ∈ ⟦ p ⟧ ↔ (p, s) ⟹ t :=
iff.intro
  (big_step_of_den p s t)
  (den_of_big_step p s t)

end lecture
