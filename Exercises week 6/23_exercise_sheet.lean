/- Exercise 2.3: Functional Programming — Monads -/

namespace exercise


/- Question 1: A state monad with failure -/

/- As usual, we start by repeating some material from the lecture. -/

class monad (M : Type → Type) extends has_bind M, has_pure M : Type 1 :=
(pure_bind {α β} (a : α) (f : α → M β) :
  pure a >>= f = f a)
(bind_pure {α} (m : M α) :
  m >>= pure = m)
(bind_assoc {α β γ} (f : α → M β) (g : β → M γ) (m : M α) :
  ((m >>= f) >>= g) = (m >>= (λa, f a >>= g)))

attribute [simp] exercise.monad.bind_pure exercise.monad.bind_assoc exercise.monad.pure_bind

open exercise.monad

instance monad_option : monad option :=
{ pure       := @option.some,
  bind       := @option.bind,
  pure_bind  := assume α β a f, by refl,
  bind_pure  := assume α m, match m with none := by refl | some a := by refl end,
  bind_assoc := assume α β γ f g m, match m with none := by refl | some a := by refl end }

/- For this exercise, we introduce a richer notion of monad that provides an `orelse` operator `<|>`
satisfying some laws, given below. `emp` denotes failure. `x <|> y` tries `x` first, falling back on
`y` on failure. -/

class monad_with_orelse (M : Type → Type) extends monad M, has_orelse M :=
(emp {} {α} : M α)
(emp_orelse {α} (a : M α) :
  (emp <|> a) = a)
(orelse_emp {α} (a : M α) :
  (a <|> emp) = a)
(orelse_assoc {α} (a b c : M α) :
  ((a <|> b) <|> c) = (a <|> (b <|> c)))
(emp_bind {α β} (f : α → M β) :
  (emp >>= f) = emp)
(bind_emp {α β} (f : M α) :
  (f >>= (λa, emp : α → M β)) = emp)

open exercise.monad_with_orelse

attribute [simp] exercise.monad_with_orelse.emp_orelse exercise.monad_with_orelse.orelse_emp
  exercise.monad_with_orelse.orelse_assoc exercise.monad_with_orelse.emp_bind
  exercise.monad_with_orelse.bind_emp

/- 1.1. We set up the `option` type constructor to be a `monad_with_orelse`. Complete the proofs
below. -/

namespace option

variables {α β γ : Type}

def orelse {α} : option α → option α → option α
| none     b := b
| (some a) _ := some a

instance : monad_with_orelse option :=
{ emp          := λα, none,
  orelse       := @option.orelse,
  emp_orelse   := assume α a, match a with some a := by refl | none := by refl end ,
  orelse_emp   := assume α a, match a with some a := by refl | none := by refl end,
  orelse_assoc := assume α a b c, match a with some a := by refl | none := by refl end,
  emp_bind     := assume α β f, by refl,
  bind_emp     := assume α β f, by ...,
  .. exercise.monad_option }

@[simp] lemma some_bind (a : α) (g : α → option β) :
  (some a >>= g) = g a := by refl

end option

/- Let us enable some convenient pattern matching syntax, by instantiating Lean's `monad_fail` type
class. -/

instance {M} [monad_with_orelse M] : monad_fail M :=
⟨λα msg, emp⟩

/- Now we can write definitions such as the following: -/

def first_of_three {M} [monad_with_orelse M] (c : M (list ℕ)) : M ℕ := do
  [n, _, _] ← c, -- look Ma, this list has three elements!
  pure n

#eval first_of_three (some [1])
#eval first_of_three (some [1, 2, 3, 4])
#eval first_of_three (some [1, 2, 3])

/- Using `monad_with_orelse` and the `monad_fail` syntax, we can give a much more consise definition
for the `sum_2_5_7` function seen in the lecture. -/

def sum_2_5_7 {M} [monad_with_orelse M] (c : M (list ℕ)) : M ℕ := do
  (_ :: n2 :: _ :: _ :: n5 :: _ :: n7 :: _) ← c,
  pure (n2 + n5 + n7)

/- 1.2. Now we are ready to define `fstate σ`: a monad with an internal state of type `σ` that can
fail (unlike `state σ`).

We start with defining `fstate σ α`, where `σ` is the type of the internal state, and `α` is the
type of the value stored in the monad. We use `option` to model failure. This means we can also use
the monadic behvior of `option` when defining the monadic opertions on `fstate`.

**Hint:** Remember that `fstate σ α` is an alias for a function type, so you can use pattern
matching and `λs, ...` to define values of type `fstate σ α`.

**Hint:** `fstate` is very similar to `state` in the lecture demonstration. You can look there for
inspiration.
-/

def fstate (σ : Type) (α : Type) := σ → option (α × σ)

/- 1.3. Define the `get` and `set` function for `fstate`, where `get` returns the state passed along
the state monad, and `set s` changes the state to `s` and returns the old state.
-/

def get {σ : Type} : fstate σ σ
| s := (s,s)

def set {σ : Type} (s : σ) : fstate σ unit
| t := ((), s)

namespace fstate

variables {σ α β γ : Type}

/- 1.4. Define the monadic operators (`bind` and `pure`) for `fstate`, in such a way that they
will satisfy the monadic laws. -/

protected def bind (f : fstate σ α) (g : α → fstate σ β) : fstate σ β
| s := function.uncurry g (f s)

-- set up the `>>=` syntax on `fstate`
instance : has_bind (fstate σ) := ⟨@fstate.bind σ⟩

@[simp] lemma bind_apply (f : fstate σ α) (g : α → fstate σ β) (s : σ) :
  (f >>= g) s = f s >>= function.uncurry g :=
by refl

protected def pure (a : α) : fstate σ α
:= sorry

-- we already setup the syntax for `pure` on `fstate`
instance : has_pure (fstate σ) := ⟨@fstate.pure σ⟩

@[simp] lemma pure_apply (a : α) (s : σ) :
  (pure a : fstate σ α) s = some (a, s) :=
by refl

/- 1.3 `fstate` is a monad:

**Hint:** `pure` and `bind` are introduced using `protected`, so their names are `fstate.pure` and
`fstate.bind`

**Hint**: `funext` is your friend when you need to prove equality between two functions.

**Hint**: Sometimes one `cases` is not enough, especially `uncurry f p` requires that `p` is a pair
of the form `(a, b)`!

**Hint**: `cases (f s)` only works when `f s` is appreaing in your goal, so you may need to unfold
some constants before you can do a `cases`.
-/

instance : monad (fstate σ) :=
{ pure_bind  :=
    sorry,
  bind_pure  :=
    sorry,
  bind_assoc :=
    sorry,
  .. fstate.has_bind, .. fstate.has_pure }

/- 1.4 `fstate` is a monad which supports failure.

**Hint**: Sometimes one `cases` is not enough, especially `uncurry f p` requires that `p` is a pair
of the form `(a, b)`!

**Hint**: `funext` is your friend when you need to prove equality between two functions.

**Hint**: parts of `fstate` are defined using the `option` monad, so parts of some proofs could
use `emp_orelse`, `orelse_emp`, `orelse_assoc`, `emp_bind`, when talking about `option`. -/

instance : monad_with_orelse (fstate σ) :=
{ emp          := λα s, none,
  orelse       := λα f g s, option.orelse (f s) (g s),
  emp_orelse   :=
    sorry,
  orelse_emp   :=
    sorry,
  orelse_assoc :=
    sorry,
  emp_bind     :=
    sorry,
  bind_emp     := assume α β f, funext $ assume s,
    sorry,
  .. exercise.fstate.exercise.monad }

@[simp] lemma orelse_apply (f g : fstate σ α) (s : σ) :
  (f <|> g) s = (f s <|> g s) :=
by refl

@[simp] lemma emp_apply (s : σ) :
  (emp : fstate σ α) s = (emp : option (α × σ)) :=
by refl

end fstate

/- Let us use `fstate`. -/

section monad

variables {M : Type → Type} [monad M] {α β : Type}

def mmap (f : α → M β) : list α → M (list β)
| []       := pure []
| (a :: l) := do
  b ← f a,
  l' ← mmap l,
  pure (b :: l')

end monad

example (l : list ℕ) : fstate ℕ (list ℕ) :=
mmap (λp : ℕ, do
  prev ← get,
  set p,
  if prev > p then
    emp
  else
    pure (p - prev)) l


/-  Question 2: Kleisli operator: pipelining monadic operations -/

section kleisli_operator

open monad

variables {M : Type → Type} [monad M] {α β γ δ : Type}
variables {f : α → M β} {g : β → M γ} {h : γ → M δ}

def kleisli (f : α → M β) (g : β → M γ) : (α → M γ) :=
λa, f a >>= g

infixr ` >=> `:90 := kleisli

/- 2.1. Prove the following equations for the Kleisli operator.

**Hint**: Remember `funext`. -/

-- `pure` is a left unit for `>=>`
lemma pure_kleisli : pure >=> f = f :=
sorry

-- `pure` is a right unit for `>=>`
lemma kleisli_pure : f >=> pure = f :=
sorry

-- `>=>` is associative
lemma kleisli_assoc : (f >=> g) >=> h = f >=> (g >=> h) :=
sorry

end kleisli_operator

end exercise
