/- Library 3.1: Program Semantics — Operational Semantics -/

/- Some auxiliary lemmas concerning logical connectives and relations -/

@[simp] lemma or_imp_distrib {p q r : Prop} : p ∨ q → r ↔ (p → r) ∧ (q → r) :=
iff.intro
  (assume h, ⟨assume hp, h (or.intro_left _ hp), assume hq, h (or.intro_right _ hq)⟩)
  (assume ⟨hp, hq⟩ h, match h with or.inl h := hp h | or.inr h := hq h end)

@[simp] lemma and_imp_distrib {p q r : Prop} : p ∧ q → r ↔ (p → q → r) :=
iff.intro
  (assume h hp hq, h ⟨hp, hq⟩)
  (assume h ⟨hp, hq⟩, h hp hq)

@[simp] lemma exists_imp_distrib {α : Sort*} {p : α → Prop} {q : Prop} :
  ((∃a, p a) → q) ↔ (∀a, p a → q) :=
iff.intro
  (assume h hp hq, h ⟨hp, hq⟩)
  (assume h ⟨hp, hq⟩, h hp hq)

lemma and_exists {α : Sort*} {p : α → Prop} {q : Prop} :
  (q ∧ (∃a, p a)) ↔ (∃a, q ∧ p a) :=
iff.intro
  (assume ⟨h₁, a, h₂⟩, ⟨a, h₁, h₂⟩)
  (assume ⟨a, h₁, h₂⟩, ⟨h₁, a, h₂⟩)

@[simp] lemma exists_false {α : Sort*} : (∃a:α, false) ↔ false :=
iff.intro (assume ⟨a, f⟩, f) (assume h, h.elim)


/-- `refl_trans r`: relexive and transitive closure of `r` -/
inductive refl_trans {α : Sort*} (r : α → α → Prop) (a : α) : α → Prop
| refl {} : refl_trans a
| tail {b c} : refl_trans b → r b c → refl_trans c

attribute [refl] refl_trans.refl

namespace refl_trans
variables {α : Sort*} {r : α → α → Prop} {a b c d : α}

@[trans] lemma trans (hab : refl_trans r a b) (hbc : refl_trans r b c) : refl_trans r a c :=
begin
  induction hbc,
  case refl_trans.refl { assumption },
  case refl_trans.tail : c d hbc hcd hac { exact hac.tail hcd }
end

lemma single (hab : r a b) : refl_trans r a b :=
refl.tail hab

lemma head (hab : r a b) (hbc : refl_trans r b c) : refl_trans r a c :=
begin
  induction hbc,
  case refl_trans.refl { exact refl.tail hab },
  case refl_trans.tail : c d hbc hcd hac { exact hac.tail hcd }
end

lemma head_induction_on {α : Sort*} {r : α → α → Prop} {b : α}
  {P : ∀(a:α), refl_trans r a b → Prop}
  {a : α} (h : refl_trans r a b)
  (refl : P b refl)
  (head : ∀{a c} (h' : r a c) (h : refl_trans r c b), P c h → P a (h.head h')) :
  P a h :=
begin
  induction h generalizing P,
  case refl_trans.refl { exact refl },
  case refl_trans.tail : b c hab hbc ih {
    apply ih,
    show P b _, from head hbc _ refl,
    show ∀a a', r a a' → refl_trans r a' b → P a' _ → P a _, from assume a a' hab hbc, head hab _
  }
end

lemma trans_induction_on {α : Sort*} {r : α → α → Prop}
  {P : ∀{a b : α}, refl_trans r a b → Prop}
  {a b : α} (h : refl_trans r a b)
  (ih₁ : ∀a, @P a a refl)
  (ih₂ : ∀{a b} (h : r a b), P (single h))
  (ih₃ : ∀{a b c} (h₁ : refl_trans r a b) (h₂ : refl_trans r b c), P h₁ → P h₂ → P (h₁.trans h₂)) :
  P h :=
begin
  induction h,
  case refl_trans.refl { exact ih₁ a },
  case refl_trans.tail : b c hab hbc ih { exact ih₃ hab (single hbc) ih (ih₂ hbc) }
end

lemma lift {β : Sort*} {p : β → β → Prop} (f : α → β) (h : ∀a b, r a b → p (f a) (f b))
  (hab : refl_trans r a b) : refl_trans p (f a) (f b) :=
hab.trans_induction_on (assume a, refl) (assume a b, single ∘ h _ _) (assume a b c _ _, trans)

lemma mono {p : α → α → Prop} :
  (∀a b, r a b → p a b) → refl_trans r a b → refl_trans p a b :=
lift id

lemma refl_trans_refl_trans_eq : refl_trans (refl_trans r) = refl_trans r :=
funext $ assume a, funext $ assume b, propext $
iff.intro
  (assume h, begin induction h, { refl }, { transitivity; assumption } end)
  (refl_trans.mono (assume a b, single))

end refl_trans
