/- Homework 3.1: Program Semantics — Operational Semantics -/

attribute [pattern] or.intro_left or.intro_right


/- Question 1: Semantics of regular expressions

Regular expression are a very popular tool for software development. Often, when textual input needs
to be analyzed it is matched against a regular expression. In this homework, we define the syntax of
regular expressions and what it means that a regular expression matches a string.

We define `regex` to represent the following grammar:

    R ::= c       — `char`: accepts one character `c`
        | ∅       — `nothing`: accepts nothing
        | ε       — `empty`: accepts the empty string
        | R ⬝ R    — `concat`: accepts the concatenation of two regexes
        | R + R   — `alt`: accepts either of two regexes
        | R*      — `star`: accept arbitrary many repetitions of a regex

Notice the rough correspondence with a WHILE language:

  `char`    ~ assignment
 (`nothing` ~ failing assertion)
  `empty`   ~ `skip`
  `concat`  ~ sequential composition
  `alt`     ~ conditional statement
  `star`    ~ while loop -/

@[derive decidable_eq]
inductive regex : Type
| char    : char → regex
| nothing : regex
| empty   : regex
| concat  : regex → regex → regex
| alt     : regex → regex → regex
| star    : regex → regex

/- `accept r s`: the regular expression `r` accepts the string `s` -/

inductive accept : regex → list char → Prop
/- accept one character -/
| char (c : char) :
  accept (regex.char c) [c]
/- accept the empty string -/
| empty :
  accept regex.empty []
/- accept two concatenated regexes -/
| concat {r₁ r₂ : regex} (s₁ s₂ : list char) (h₁ : accept r₁ s₁) (h₂ : accept r₂ s₂) :
  accept (regex.concat r₁ r₂) (s₁ ++ s₂)
/- accept the left alternative -/
| alt_left {r₁ r₂ : regex} (s : list char) (h : accept r₁ s) :
  accept (regex.alt r₁ r₂) s
/- accept the right alternative -/
| alt_right {r₁ r₂ : regex} (s : list char) (h : accept r₂ s) :
  accept (regex.alt r₁ r₂) s
/- accepts the empty string; this is the base case of `R*` -/
| star_base {r : regex} : accept (regex.star r) []
/- accepts `R` followed again by `R*`; this is the induction step of `R*` -/
| star_step {r : regex} (s s' : list char) (h₁ : accept r s) (h₂ : accept (regex.star r) s') :
  accept (regex.star r) (s ++ s')

/- 1.1. Explain why there is no rule for `nothing`. -/

/- Answer: There is no input nor output. So it would be weird to have a rule for nothing, as there is nothing.. -/

/- 1.2. Prove the following inversion rules.

These proofs are very similar to the inversion rules in the lecture and in Question 2.1 of the
exercise. -/

variables {s s₁ s₂ : list char} {r r₁ r₂  : regex} {c : char}

@[simp] lemma accept_char : accept (regex.char c) s ↔ s = [c] :=
begin
  apply iff.intro,
  cases s,
  simp,
  intro s,
  cases s,
  simp,
  intro a,
  cases a,
  simp,
  intro b,
  cases b,
  exact accept.char c
end

@[simp] lemma accept_nothing : ¬ accept regex.nothing s:=
begin
  intro a,
  cases s,
  repeat {cases a}
end

@[simp] lemma accept_empty : accept regex.empty s ↔ s = [] :=
begin
  apply iff.intro,
  intro a,
  cases a,
  refl,
  intro s,
  cases s,
  exact accept.empty
end

@[simp] lemma accept_concat :
  accept (regex.concat r₁ r₂) s ↔ (∃s₁ s₂, accept r₁ s₁ ∧ accept r₂ s₂ ∧ s = s₁ ++ s₂) :=
  begin
  apply iff.intro,
  intro a,
  cases a,
  apply exists.intro a_s₁,
  apply exists.intro a_s₂,
  apply and.intro,
  assumption,
  apply and.intro,
  assumption,
  induction a,
  exact accept.concat a_s₁ a_s₂ a_h₁ a_h₂

  end

@[simp] lemma accept_alt :
  accept (regex.alt r₁ r₂) s ↔ (accept r₁ s ∨ accept r₂ s) :=
begin
  apply iff.intro,
  intro a,
  cases a,
  cases a_h,
  apply or.inl,
  assumption,
  apply or.inl,
  assumption,
  apply or.inl,
  assumption,
  apply or.inl,
  assumption,
  apply or.inl,
  assumption,
  apply or.inl,
  assumption,
  apply or.inl,
  assumption,
  apply or.inr,
  assumption,
  intro b,
  cases b,
  exact accept.alt_left s b ,
  exact accept.alt_right s b 
end

lemma accept_star :
  accept (regex.star r) s ↔
  (s = [] ∨ (∃s₁ s₂, accept r s₁ ∧ accept (regex.star r) s₂ ∧ s = s₁ ++ s₂)) :=
begin
apply iff.intro,
intro acc,
cases s,
simp,
repeat{simp[accept.star_base, accept.star_step]},
repeat {apply exists.intro s_tl},
apply and.intro,
cases s_tl,
cases r,
exact accept.empty,

end

/- 1.3 **optional**. Prove a more sophisticated version of `accept_star`.

The previous rule `accept_star` has the problem that in the induction step, the accepted string for
`r` could be empty. Now we want to **enforce** that the it is not empty, _without loss of
generality_.

*Hint*: In contrast to the other inversion rules, you now need to perform an induction. But the
arguments in our induction hypothesis `accept (regex.star r) (c :: s)` are not variables. So you
will need to generalize them. You can use `cases` to cope with the parts where the regex you handle
is not of the form `regex.star r`. In the `accept.star_step` case, you might need to split on the
string first, and then use `cases` on the second generalized equality. -/

lemma accept_star_cons :
  accept (regex.star r) (c :: s) →
  ∃s₁ s₂ : list char, accept r (c :: s₁) ∧ accept (regex.star r) s₂ ∧ s = s₁ ++ s₂ :=
sorry


/- Question 2 **optional**: Equivalence and matching of regular expressions -/

/- We can prove equivalence between regular expressions, just like between programs. Two
regular expressions are equivalent if they accept the same set of strings. -/

def regex_equiv (r₁ r₂ : regex) : Prop :=
∀s, accept r₁ s ↔ accept r₂ s

local infix ` ≈ ` := regex_equiv

/- Program equivalence is a equivalence relation, i.e. it is reflexive, symmetric, and
transitive. -/

@[refl] lemma regex_equiv.refl :
  r ≈ r :=
assume s, by refl

@[symm] lemma regex_equiv.symm :
  r₁ ≈ r₂ → r₂ ≈ r₁ :=
assume h s, (h s).symm

@[trans] lemma regex_equiv.trans {r₃} (h₁₂ : r₁ ≈ r₂) (h₂₃ : r₂ ≈ r₃) :
  r₁ ≈ r₃ :=
assume s, iff.trans (h₁₂ s) (h₂₃ s)

/- 2.1 **optional**. Prove the following regular expression equivalences. -/

lemma concat_empty_left : regex.concat regex.empty r ≈ r :=
sorry

/- **Hint**: Below, you need to rewrite at some point `x ++ [] = x` (either
using `rw` or `simp`). Depending on your approach you may be required to
introduce an intermediate goal. Remember `simp [...] at h` or `rw [...] at h`
allows you to rewrite a hypothesis. -/

lemma concat_empty_right : regex.concat r regex.empty ≈ r :=
sorry

lemma alt_idem : regex.alt r r ≈ r :=
sorry

lemma star_unfold : regex.star r ≈ regex.alt regex.empty (regex.concat r (regex.star r)) :=
sorry

/- **Hint**: For the next proof, you will probably need induction. -/

lemma star_congr_aux (hr : r₁ ≈ r₂) : accept (regex.star r₁) s → accept (regex.star r₂) s :=
sorry

/- **Hint**: For the next proof, you will probably need `star_congr_aux` and `regex.symm`. -/

lemma star_congr (hr : r₁ ≈ r₂) : regex.star r₁ ≈ regex.star r₂ :=
sorry

/- The `match_regex` function below matches a regular expression using Brzozowski derivatives. See
https://en.wikipedia.org/wiki/Brzozowski_derivative for details. -/

@[simp] def accepts_empty : regex → bool
| (regex.char c)       := ff
| regex.nothing        := ff
| regex.empty          := tt
| (regex.concat r₁ r₂) := accepts_empty r₁ && accepts_empty r₂
| (regex.alt r₁ r₂)    := accepts_empty r₁ || accepts_empty r₂
| (regex.star r)       := tt

lemma accepts_empty_iff : ∀r : regex, accepts_empty r = tt ↔ accept r []
| (regex.char c)       := by simp
| regex.nothing        := by simp
| regex.empty          := by simp
| (regex.concat r₁ r₂) :=
  begin
    simp [accepts_empty_iff r₁, accepts_empty_iff r₂],
    exact iff.intro
      (assume ⟨h₁, h₂⟩, ⟨[], [], h₁, h₂, rfl⟩)
      (assume h, match h with ⟨[], [], h₁, h₂, rfl⟩ := ⟨h₁, h₂⟩ end)
  end
| (regex.alt r₁ r₂)    := by simp [accepts_empty_iff r₁, accepts_empty_iff r₂]
| (regex.star r)       := by simp; constructor

@[simp] def deriv : regex → char → regex
| (regex.char c')      c := if c = c' then regex.empty else regex.nothing
| regex.nothing        _ := regex.nothing
| regex.empty          _ := regex.nothing
| (regex.concat r₁ r₂) c :=
  if accepts_empty r₁ = tt
  then regex.alt (regex.concat (deriv r₁ c) r₂) (deriv r₂ c)
  else regex.concat (deriv r₁ c) r₂
| (regex.alt r₁ r₂)    c := regex.alt (deriv r₁ c) (deriv r₂ c)
| (regex.star r)       c := regex.concat (deriv r c) (regex.star r)

def match_regex : regex → list char → bool
| r []       := accepts_empty r
| r (c :: s) := match_regex (deriv r c) s

/- 2.2 **optional**. Fill in the `sorry` placeholders below. -/

lemma accept_deriv : ∀r : regex, ∀c s, accept (deriv r c) s ↔ accept r (c :: s)
| (regex.char c')      c s :=
  sorry
| regex.nothing        c s :=
  sorry
| regex.empty          c s :=
  sorry
| (regex.concat r₁ r₂) c s :=
  begin
    by_cases h₁ : accepts_empty r₁ = tt;
      simp [h₁, accept_deriv r₂, accept_deriv r₁];
      simp [accepts_empty_iff] at h₁,
    sorry,  -- in one direction, you will need to make a case distinction on the string
    sorry
  end
| (regex.alt r₁ r₂)    c s := by simp [accept_deriv r₂, accept_deriv r₁]
| (regex.star r)       c s :=
  begin
    rw [accept_star],
    sorry  -- for one direction, you will probably need `accept_star_cons`
  end
