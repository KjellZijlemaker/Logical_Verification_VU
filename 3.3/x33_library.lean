/- Library 3.3: Programming Semantics — Denotational Semantics -/

/- This file contains some basic material for the Hoare logic lecture, exercise, and homework.

This file contains the following concepts:

* `state`: representing the state space of an imperative program (defined as `string → ℕ`)
  * `∅` is the empty state; mapping every variable to `0`
  * `s.update n v` or `s & n ::= v`: replace the name `n` in the state `s` by value `v`
  * `s n` variable `n` of state `s`

* `program` syntax for WHILE programs over `state` as state space.
  This is a slight modification of the lecture 3.1. Instead of over an arbitrary state space `σ` we
  are now fixed on `state`; and also `assign` only allows changing one variable.

* `(p, s) ⟹ t`: big-step semantics over `program`

It is all under the `lecture` namespace. -/

universes u

attribute [pattern] or.intro_left or.intro_right

meta def tactic.dec_trivial := `[exact dec_trivial]

@[simp] lemma not_not_iff (p : Prop) [decidable p] : ¬ (¬ p) ↔ p :=
by by_cases p; simp [h]

@[simp] lemma and_imp (p q r : Prop) : ((p ∧ q) → r) ↔ (p → q → r) :=
iff.intro
  (assume h hp hq, h ⟨hp, hq⟩)
  (assume h ⟨hp, hq⟩, h hp hq)

@[simp] lemma exists_false_iff {α : Sort u} : (∃a:α, false) ↔ false :=
iff.intro
  (assume ⟨a, h⟩, h)
  (assume h, h.elim)

@[simp] lemma mem_set_of {α : Type} (p : α → Prop) (a : α) : a ∈ {a | p a} ↔ p a :=
by refl

@[simp] lemma mem_union {α : Type} (s t : set α) (a : α) : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t :=
by refl

namespace lecture

/- `state` to represent state spaces -/

def state := string → ℕ

def state.update (name : string) (val : ℕ) (s : state) : state :=
λn, if n = name then val else s n

notation s ` & ` n ` ::= ` v := state.update n v s

namespace state

instance : has_emptyc state := ⟨λ_, 0⟩

@[simp] lemma update_apply (name : string) (val : ℕ) (s : state) :
  (s & name ::= val) name = val :=
if_pos rfl

@[simp] lemma update_apply_ne (name name' : string) (val : ℕ) (s : state)
  (h : name' ≠ name . tactic.dec_trivial):
  (s & name ::= val) name' = s name' :=
if_neg h

@[simp] lemma update_override (name : string) (val₁ val₂ : ℕ) (s : state) :
  (s & name ::= val₂ & name ::= val₁) = (s & name ::= val₁) :=
by funext name'; by_cases name' = name; simp [h]

@[simp] lemma update_swap
  (name₁ name₂ : string) (val₁ val₂ : ℕ) (s : state) (h : name₁ ≠ name₂ . tactic.dec_trivial):
  (s & name₂ ::= val₂ & name₁ ::= val₁) = (s & name₁ ::= val₁ & name₂ ::= val₂) :=
by funext name'; by_cases h₁ : name' = name₁; by_cases h₂ : name' = name₂; simp * at *

end state

example (s : state) : (s & "a" ::= 0 & "a" ::= 2) = (s & "a" ::= 2) :=
by simp

example (s : state) : (s & "a" ::= 0 & "b" ::= 2) = (s & "b" ::= 2 & "a" ::= 0) :=
by simp

/- A WHILE programming language -/

inductive program : Type
| skip {} : program
| assign  : string → (state → ℕ) → program
| seq     : program → program → program
| ite     : (state → Prop) → program → program → program
| while   : (state → Prop) → program → program

infixr ` ;; `:90 := program.seq

open program

/- We use the **big step** semantics -/

inductive big_step : (program × state) → state → Prop
| skip {s} :
  big_step (skip, s) s
| assign {n f s} :
  big_step (assign n f, s) (s.update n (f s))
| seq {p₁ p₂ s u} (t) (h₁ : big_step (p₁, s) t) (h₂ : big_step (p₂, t) u) :
  big_step (seq p₁ p₂, s) u
| ite_true {c : state → Prop} {p₁ p₀ s t} (hs : c s) (h : big_step (p₁, s) t) :
  big_step (ite c p₁ p₀, s) t
| ite_false {c : state → Prop} {p₁ p₀ s t} (hs : ¬ c s) (h : big_step (p₀, s) t) :
  big_step (ite c p₁ p₀, s) t
| while_true {c : state → Prop} {p s u} (t) (hs : c s) (hp : big_step (p, s) t)
  (hw : big_step (while c p, t) u) :
  big_step (while c p, s) u
| while_false {c : state → Prop} {p s} (hs : ¬ c s) : big_step (while c p, s) s

infix ` ⟹ `:110 := big_step

section inversion_rules

variables (s t : state) (n : string) (p p₀ p₁ p₂ : program)
  (c : state → Prop) (f : state → ℕ)

@[simp] lemma big_step_skip_iff :
  (skip, s) ⟹ t ↔ t = s :=
iff.intro
  (assume h, match t, h with _, big_step.skip := by refl       end)
  (assume h, match t, h with _, rfl           := big_step.skip end)

@[simp] lemma big_step_assign_iff :
  (assign n f, s) ⟹ t ↔ t = s.update n (f s) :=
iff.intro
  (assume h, match t, h with _, big_step.assign := rfl end)
  (assume h, match t, h with _, rfl := big_step.assign end)

@[simp] lemma big_step_seq_iff :
  (seq p₁ p₂, s) ⟹ t ↔ (∃u, (p₁, s) ⟹ u ∧ (p₂, u) ⟹ t) :=
iff.intro
  (assume h, match h with big_step.seq u h₁ h₂ := ⟨u, h₁, h₂⟩ end)
  (assume h, match h with ⟨u, h₁, h₂⟩ := big_step.seq u h₁ h₂ end)

@[simp] lemma big_step_ite_iff :
  (ite c p₁ p₀, s) ⟹ t ↔ ((c s ∧ (p₁, s) ⟹ t) ∨ (¬ c s ∧ (p₀, s) ⟹ t)) :=
iff.intro
  (assume h, match h with
  | big_step.ite_true  hs h := or.intro_left _ ⟨hs, h⟩
  | big_step.ite_false hs h := or.intro_right _ ⟨hs, h⟩
  end)
  (assume h, match h with
  | or.intro_left  _ ⟨hs, h⟩ := big_step.ite_true hs h
  | or.intro_right _ ⟨hs, h⟩ := big_step.ite_false hs h
  end)

lemma big_step_while_iff :
  (while c p, s) ⟹ t ↔ (∃u, c s ∧ (p, s) ⟹ u ∧ (while c p, u) ⟹ t) ∨ (¬ c s ∧ t = s) :=
iff.intro
  (assume h, match t, h with
  | t, big_step.while_true u hs h₁ h₂ := or.intro_left _ ⟨u, hs, h₁, h₂⟩
  | s, big_step.while_false hs := or.intro_right _ ⟨hs, rfl⟩
  end)
  (assume h, match t, h with
  | _, or.intro_left  _ ⟨u, hs, h₁, h₂⟩ := big_step.while_true u hs h₁ h₂
  | _, or.intro_right _ ⟨hs, rfl⟩ := big_step.while_false hs
  end)

@[simp] lemma big_step_while_true_iff (hs : c s) :
  (while c p, s) ⟹ t ↔ (∃u, (p, s) ⟹ u ∧ (while c p, u) ⟹ t) :=
by rw [big_step_while_iff]; simp [hs]

@[simp] lemma big_step_while_false_iff (hs : ¬ c s) :
  (while c p, s) ⟹ t ↔ t = s :=
by rw [big_step_while_iff]; simp [hs]

end inversion_rules

end lecture
