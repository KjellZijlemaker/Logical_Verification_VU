/- Lecture 3.1: Program Semantics — Operational Semantics -/

import .x31_library

attribute [pattern] or.intro_left or.intro_right


/- A WHILE programming language -/

section syntax

inductive program (σ : Type) : Type
| skip {} : program
| assign  : (σ → σ) → program
| seq     : program → program → program
| ite     : (σ → Prop) → program → program → program
| while   : (σ → Prop) → program → program

end syntax


/- Big-step semantics -/

open program

section semantics

variables {σ : Type} {c : σ → Prop} {f : σ → σ} {p p₀ p₁ p₂ : program σ} {s s₀ s₁ s₂ t u : σ}

/- `big_step p s s'`: when started in `s`, program `p` terminates in `s'`. -/

inductive big_step : (program σ × σ) → σ → Prop
| skip {s} :
  big_step (skip, s) s
| assign {f s} :
  big_step (assign f, s) (f s)
| seq {p₁ p₂ s u} (t) (h₁ : big_step (p₁, s) t) (h₂ : big_step (p₂, t) u) :
  big_step (seq p₁ p₂, s) u
| ite_true {c : σ → Prop} {p₁ p₀ s t} (hs : c s) (h : big_step (p₁, s) t) :
  big_step (ite c p₁ p₀, s) t
| ite_false {c : σ → Prop} {p₁ p₀ s t} (hs : ¬ c s) (h : big_step (p₀, s) t) :
  big_step (ite c p₁ p₀, s) t
| while_true {c : σ → Prop} {p s u} (t) (hs : c s) (hp : big_step (p, s) t)
  (hw : big_step (while c p, t) u) :
  big_step (while c p, s) u
| while_false {c : σ → Prop} {p s} (hs : ¬ c s) : big_step (while c p, s) s

/- Mixfix notation for `big_step`:

    (p, s) ⟹ s'  :=  big_step (p, s) s'.

`⟹` is entered as `\==>`. -/

infix ` ⟹ `:110 := big_step

section tactics

open tactic

/- Finds two local hypotheses `hnp : ¬ p` and `hp : p` and solves the goal by contradiction -/
meta def find_absurd : tactic unit := do
  hs ← local_context,
  hs.mfirst $ λhn, do
    `(¬ %%p) ← infer_type hn,
    (hs.mfirst $ λh, do
      p' ← infer_type h,
      is_def_eq p p',
      to_expr ``(false.elim (%%hn %%h)) >>= exact)

/- For a `ih : ∀x, p x → q x`, finds all matching `h : p t` and resolves `ih` with each `h` -/
meta def resolve_all : tactic unit := do
  hs ← local_context,
  hs.mfirst $ λih, do
    ([x, h'], g) ← infer_type ih >>= mk_local_pis,
    p ← mk_pattern [] [x] h' [] [x],
    l ← hs.reverse.mmap $ λh, (do
      ([], [x']) ← match_pattern p h,
      tactic.note ih.local_pp_name none (ih x' h),
      pure tt) <|> pure ff,
    if l.bor then clear ih else skip

/- Resolves all `ih : ∀x, p x → q x` with all `h : p t` and substitutes all occurrences of `x = t`
or `t = x` -/
meta def tactic.interactive.resolve_subst : tactic unit :=
repeat (resolve_all >> subst_vars)

end tactics


/- The `big_step` semantics is deterministic: two terminating program executions result in the same
output -/

lemma big_step_unique (ht : (p, s) ⟹ t) (hu : (p, s) ⟹ u) : u = t :=
begin
  induction ht generalizing u hu;
    cases hu;
    resolve_subst;
    try { refl <|> find_absurd }
end

lemma not_cond_of_big_step_while : (while c p, s) ⟹ t → ¬ c t :=
begin
  generalize eq_ps : (while c p, s) = ps,
  intro h,
  induction h generalizing s eq_ps;
    cases eq_ps,
  { apply h_ih_hw, refl },
  { assumption }
end


/- Inversion rules for `⟹` -/

@[simp] lemma big_step_skip_iff :
  (skip, s) ⟹ t ↔ t = s :=
iff.intro
  (assume h, match t, h with _, big_step.skip := by refl       end)
  (assume h, match t, h with _, rfl           := big_step.skip end)

@[simp] lemma big_step_assign_iff :
  (assign f, s) ⟹ t ↔ t = f s :=
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


/- Small-step semantics -/

inductive small_step : program σ × σ → program σ × σ → Prop
| assign {f s} :
  small_step (assign f, s) (skip, f s)
| seq_step {p₁ p₂ s s'} (p) :
  small_step (p₁, s) (p, s') → small_step (seq p₁ p₂, s) (seq p p₂, s')
| seq_skip {p s} :
  small_step (seq skip p, s) (p, s)
| ite_true {c : σ → Prop} {p₁ p₀ s} :
  c s → small_step (ite c p₁ p₀, s) (p₁, s)
| ite_false {c : σ → Prop} {p₁ p₀ s} :
  ¬ c s → small_step (ite c p₁ p₀, s) (p₀, s)
| while {c : σ → Prop} {p s} :
  small_step (while c p, s) (ite c (seq p (while c p)) skip, s)

/- Mixfix notations for `small_step`:

    ps ⇒ qt   :=  small_step ps qt
    ps ⇒* qt  :=  refl_trans small_step ps qt -/

infixr ` ⇒ `  := small_step
infixr ` ⇒* ` : 100 := refl_trans small_step


/- Inversion rules for `⇒` -/

@[simp] lemma small_step_skip : ¬ ((skip, s) ⇒ (p, t)) :=
assume h, match h with end

lemma small_step_seq_iff {v : program σ × σ} :
  (seq p₁ p₂, s) ⇒ v ↔ (∃p t, (p₁, s) ⇒ (p, t) ∧ v = (seq p p₂, t)) ∨ (p₁ = skip ∧ v = (p₂, s)) :=
iff.intro
  (assume h, match p₁, v, h with
    | _, (_, t), small_step.seq_step p h := or.intro_left _ ⟨p, t, h, rfl⟩
    | _, _,      small_step.seq_skip     := or.intro_right _ ⟨rfl, rfl⟩
    end)
  (assume h, match p₁, v, h with
    | _, _, or.intro_left _ ⟨p, t, h, rfl⟩ := small_step.seq_step p h
    | _, _, or.intro_right _ ⟨rfl, rfl⟩    := small_step.seq_skip
    end)

@[simp] lemma small_step_ite_iff {v : program σ × σ} :
  (ite c p₁ p₂, s) ⇒ v ↔ (c s ∧ v = (p₁, s)) ∨ (¬ c s ∧ v = (p₂, s)) :=
iff.intro
  (assume h, match v, h with
  | _, small_step.ite_true  h := or.intro_left _ ⟨h, rfl⟩
  | _, small_step.ite_false h := or.intro_right _ ⟨h, rfl⟩
  end)
  (assume h, match v, h with
  | _, or.intro_left  _ ⟨h, rfl⟩ := small_step.ite_true h
  | _, or.intro_right _ ⟨h, rfl⟩ := small_step.ite_false h
  end)


/- Connection between `_ ⇒* _` and `⟹` -/

lemma refl_trans_small_step_seq (h : (p₁, s) ⇒* (skip, u)) :
  (seq p₁ p₂, s) ⇒* (seq skip p₂, u) :=
h.lift (λp:program σ × σ, (seq p.1 p₂, p.2)) $
  assume ⟨p₁, s⟩ ⟨p₂, t⟩, small_step.seq_step _

lemma big_step_imp_refl_trans_small_step (h : (p, s) ⟹ t) :
  (p, s) ⇒* (skip, t) :=
begin
  induction h,
  case big_step.skip { refl },
  case big_step.assign { exact refl_trans.single small_step.assign },
  case big_step.seq : p₁ p₂ s t u h₁ h₂ ih₁ ih₂ {
    transitivity,
    exact refl_trans_small_step_seq ih₁,
    exact ih₂.head small_step.seq_skip
  },
  case big_step.ite_true : c p₁ p₂ s t hs hst ih {
    exact ih.head (small_step.ite_true hs)
  },
  case big_step.ite_false : c p₁ p₂ s t hs hst ih {
    exact ih.head (small_step.ite_false hs)
  },
  case big_step.while_true : c p s t u hs h₁ h₂ ih₁ ih₂ {
    exact (refl_trans.head (small_step.while) $
      refl_trans.head (small_step.ite_true hs) $
      (refl_trans_small_step_seq ih₁).trans $
      refl_trans.head small_step.seq_skip $
      ih₂)
  },
  case big_step.while_false : c p s hs {
    exact (refl_trans.single small_step.while).tail (small_step.ite_false hs)
  }
end

lemma big_step_of_small_step_of_big_step :
  (p₀, s₀) ⇒ (p₁, s₁) → (p₁, s₁) ⟹ s₂ → (p₀, s₀) ⟹ s₂ :=
begin
  generalize hv₀ : (p₀, s₀) = v₀,
  generalize hv₁ : (p₁, s₁) = v₀,
  intro h,
  induction h generalizing p₀ s₀ p₁ s₁ s₂;
    cases hv₁; clear hv₁;
    cases hv₀; clear hv₀;
    simp [*, big_step_while_true_iff] {contextual := tt},
  { intros u h₁ h₂, exact ⟨u, h_ih rfl rfl h₁, h₂⟩ },
  { intro h, exact ⟨_, rfl, h⟩ }
end

lemma refl_trans_small_step_imp_big_step :
  (p, s) ⇒* (skip, t) → (p, s) ⟹ t :=
begin
  generalize hv₀ : (p, s) = v₀,
  intro h,
  induction h
    using refl_trans.head_induction_on
    with v₀ v₁ h h' ih
    generalizing p s;
    cases hv₀;
    clear hv₀,
  { exact big_step.skip },
  { cases v₁ with p' s',
    specialize ih rfl,
    exact big_step_of_small_step_of_big_step h ih }
end

lemma big_step_iff_refl_trans_small_step :
  (p, s) ⟹ t ↔ (p, s) ⇒* (skip, t) :=
iff.intro
  big_step_imp_refl_trans_small_step
  refl_trans_small_step_imp_big_step

end semantics
