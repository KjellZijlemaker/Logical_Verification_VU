/- Lecture 3.2: Program Semantics — Hoare Logic -/

-- loads big-step semantics `(p, s) ⟹ t` over `state` as state space
import .x32_library

namespace lecture

open program

variables
  {c : state → Prop} {f : state → ℕ} {n : string}
  {p p₀ p₁ p₂ : program} {s s₀ s₁ s₂ t u : state}
  {P P' P₁ P₂ P₃ Q Q' : state → Prop}


/- Hoare triples `{* P *} p {* Q *}` for partial correctness -/

def partial_hoare (P : state → Prop) (p : program) (Q : state → Prop) : Prop :=
∀s t, P s → (p, s) ⟹ t → Q t

notation `{* ` P : 1 ` *} ` p : 1 ` {* ` Q : 1 ` *}` := partial_hoare P p Q


/- Introduction rules for Hoare triples -/

namespace partial_hoare

lemma skip_intro :
  {* P *} skip {* P *} :=
begin
  intros s t hs hst,
  cases hst,
  assumption
end

lemma assign_intro (P : state → Prop) :
  {* λs, P (s.update n (f s)) *} assign n f {* P *} :=
begin
  intros s t P hst,
  cases hst,
  assumption
end

lemma seq_intro (h₁ : {* P₁ *} p₁ {* P₂ *}) (h₂ : {* P₂ *} p₂ {* P₃ *}) :
  {* P₁ *} p₁ ;; p₂ {* P₃ *} :=
begin
  intros s t P hst,
  cases hst,
  apply h₂ _ _ _ hst_h₂,
  apply h₁ _ _ _ hst_h₁,
  assumption
end

lemma ite_intro (h₁ : {* λs, P s ∧ c s *} p₁ {* Q *}) (h₂ : {* λs, P s ∧ ¬ c s *} p₂ {* Q *}) :
  {* P *} ite c p₁ p₂ {* Q *} :=
begin
  intros s t hs hst,
  cases hst,
  { apply h₁ _ _ _ hst_h,
    exact ⟨hs, hst_hs⟩ },
  { apply h₂ _ _ _ hst_h,
    exact ⟨hs, hst_hs⟩ },
end

lemma while_intro (P : state → Prop) (h₁ : {* λs, P s ∧ c s *} p {* P *}) :
  {* P *} while c p {* λs, P s ∧ ¬ c s *} :=
begin
  intros s t hs,
  generalize eq : (while c p, s) = ps,
  intro hst,
  induction hst generalizing s; cases eq,
  { apply hst_ih_hw hst_t _ rfl,
    exact h₁ _ _ ⟨hs, hst_hs⟩ hst_hp },
  { exact ⟨hs, hst_hs⟩ }
end

lemma consequence (h : {* P *} p {* Q *}) (hp : ∀s, P' s → P s) (hq : ∀s, Q s → Q' s) :
  {* P' *} p {* Q' *} :=
assume s t hs hst, hq _ $ h s t (hp s hs) hst

lemma consequence_left (P' : state → Prop) (h : {* P *} p {* Q *}) (hp : ∀s, P' s → P s) :
  {* P' *} p {* Q *} :=
consequence h hp (assume s hs, hs)

lemma consequence_right (Q : state → Prop) (h : {* P *} p {* Q *}) (hq : ∀s, Q s → Q' s) :
  {* P *} p {* Q' *} :=
consequence h (assume s hs, hs) hq

/- Many of the above rules are nonlinear (i.e. their conclusions contain repeated variables). This
makes them inconvenient to apply. We combine some of the previous rules with `consequence` to derive
linear rules. -/

lemma skip_intro' (h : ∀s, P s → Q s):
  {* P *} skip {* Q *} :=
consequence skip_intro h (assume s hs, hs)

lemma assign_intro' (h : ∀s, P s → Q (s.update n (f s))):
  {* P *} assign n f {* Q *} :=
consequence (assign_intro Q) h (assume s hs, hs)

lemma seq_intro' (h₂ : {* P₂ *} p₂ {* P₃ *}) (h₁ : {* P₁ *} p₁ {* P₂ *}) :
  {* P₁ *} p₁ ;; p₂ {* P₃ *} :=
seq_intro h₁ h₂

lemma while_intro_inv (I : state → Prop)
  (h₁ : {* λs, I s ∧ c s *} p {* I *}) (hp : ∀s, P s → I s) (hq : ∀s, ¬ c s → I s → Q s) :
  {* P *} while c p {* Q *} :=
consequence (while_intro I h₁) hp (assume s ⟨hs, hnc⟩, hq s hnc hs)

end partial_hoare


/- Example: `SWAP`

Exchanges the values of variables `a` and `b`. -/

section SWAP

open partial_hoare

def SWAP : program :=
assign "t" (λs, s "a") ;;
assign "a" (λs, s "b") ;;
assign "b" (λs, s "t")

lemma SWAP_correct (x y : ℕ) :
  {* λs, s "a" = x ∧ s "b" = y *} SWAP {* λs, s "a" = y ∧ s "b" = x *} :=
begin
  apply seq_intro',
  apply seq_intro',
  apply assign_intro,
  apply assign_intro,
  apply assign_intro',
  /- The remaining goal looks horrible. But `simp` can simplify it dramatically, and with contextual
  rewriting (i.e. using assumptions in the goal as rewrite rules), it can solve it. -/
  simp {contextual := tt},
end

end SWAP


/- Example: `ADD`

Computes `m + n`, leaving the result in `n`, using only these primitive operations: `n + 1`,
`n - 1`, and `n ≠ 0`. -/

section ADD

open partial_hoare

def ADD : program :=
while (λs, s "n" ≠ 0)
( assign "n" (λs, s "n" - 1) ;;
  assign "m" (λs, s "m" + 1) )

lemma ADD_correct (n m : ℕ) :
  {* λs, s "n" = n ∧ s "m" = m *} ADD {* λs, s "m" = n + m *} :=
begin
  -- `refine` is like `exact`, but it lets us specify holes to be filled later
  refine while_intro_inv (λs, s "n" + s "m" = n + m) _ _ _,
  apply seq_intro',
  apply assign_intro,
  apply assign_intro',
  { simp,
    -- puhh this looks much better: `simp` removed all `update`s
    intros s hnm hn0,
    rw ←hnm,
    -- subtracting on `ℕ` is annoying
    cases s "n",
    { contradiction },
    { simp [nat.succ_eq_add_one] } },
  { simp {contextual := tt} },
  { simp [not_not_iff] {contextual := tt} }
end

end ADD


/- Annotated while loop -/

def program.while_inv (I : state → Prop) (c : state → Prop) (p : program) : program :=
while c p

open program -- makes `program.while_inv` available as `while_inv`

namespace partial_hoare

/- `while_inv` rules use the invariant annotation -/

lemma while_inv_intro {I : state → Prop}
  (h₁ : {* λs, I s ∧ c s *} p {* I *}) (hq : ∀s, ¬ c s → I s → Q s) :
  {* I *} while_inv I c p {* Q *} :=
while_intro_inv I h₁ (assume s hs, hs) hq

lemma while_inv_intro' {I : state → Prop}
  (h₁ : {* λs, I s ∧ c s *} p {* I *}) (hp : ∀s, P s → I s) (hq : ∀s, ¬ c s → I s → Q s) :
  {* P *} while_inv I c p {* Q *} :=
while_intro_inv I h₁ hp hq

end partial_hoare

end lecture

namespace tactic.interactive

open lecture.partial_hoare lecture tactic

meta def is_meta {elab : bool} : expr elab → bool
| (expr.mvar _ _ _) := tt
| _                 := ff


/- Verification condition generator -/

meta def vcg : tactic unit := do
  t ← target,
  match t with
  | `({* %%P *} %%p {* _ *}) :=
    match p with
    | `(program.skip)            := applyc (if is_meta P then ``skip_intro else ``skip_intro')
    | `(program.assign _ _)      := applyc (if is_meta P then ``assign_intro else ``assign_intro')
    | `(program.ite _ _ _)       := do applyc ``ite_intro; vcg
    | `(program.seq _ _)         := do applyc ``seq_intro'; vcg
    | `(program.while_inv _ _ _) :=
      do applyc (if is_meta P then ``while_inv_intro else ``while_inv_intro'); vcg
    | _                          := fail (to_fmt "cannot analyze " ++ to_fmt p)
    end
  | _ := skip  -- do nothing if the goal is not a Hoare triple
  end

end tactic.interactive

namespace lecture

open program

example (n m : ℕ) :
  {* λs, s "n" = n ∧ s "m" = m *} ADD {* λs, s "n" = 0 ∧ s "m" = n + m *} :=
begin
  -- use `show` to annotate the while loop with an invariant
  show {* λs, s "n" = n ∧ s "m" = m *}
      while_inv (λs, s "n" + s "m" = n + m) (λs, s "n" ≠ 0)
      ( assign "n" (λs, s "n" - 1) ;;
        assign "m" (λs, s "m" + 1) )
    {* λs, s "n" = 0 ∧ s "m" = n + m *},
  vcg;
    simp {contextual := tt},
  intros s hnm hn,
  rw ←hnm,
  cases s "n",
  { contradiction },
  { simp [nat.succ_eq_add_one] }
end

end lecture
