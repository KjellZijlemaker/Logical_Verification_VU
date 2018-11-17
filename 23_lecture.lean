/- Lecture 2.3: Functional Programming — Monads -/

namespace lecture


/- Part 1: Failure is an `option` -/

/- Motivating examples -/

namespace problem

/- Implement `sum_2_5_7 l`: sum up the 2nd, 5th, and 7th elements of list `l`.

How to handle the case when the list has fewer than 7 elements? _Solution:_ Return `option`. -/

def sum_2_5_7_v1 (l : list ℕ) : option ℕ :=
match list.nth l 1 with
| some n2 :=
  match list.nth l 4 with
  | some n5 :=
    match list.nth l 6 with
    | some n7 := some (n2 + n5 + n7)
    | none    := none
    end
  | none    := none
  end
| none    := none
end

def bind {α : Type} {β : Type} : option α → (α → option β) → option β
| none     b := none
| (some a) b := b a

#check λ(f g h : ℕ → ℕ) x, h $ g $ f $ x

def sum_2_5_7_v2 (l : list ℕ) : option ℕ :=
bind (list.nth l 1) $
  λn2, bind (list.nth l 4) $
    λn5, bind (list.nth l 6) $
      λn7, some (n2 + n5 + n7)

#check has_bind.bind -- `do` notation
#check (>>=)

def sum_2_5_7_v3 (l : list ℕ) : option ℕ :=
list.nth l 1 >>=
  λn2, list.nth l 4 >>=
    λn5, list.nth l 6 >>=
      λn7, some (n2 + n5 + n7)

def sum_2_5_7_v4 (l : list ℕ) : option ℕ :=
do
  n2 ← list.nth l 1,
  n5 ← list.nth l 4,
  n7 ← list.nth l 6,
  some (n2 + n5 + n7)

#check @pure


/- The monadic laws for `option` -/

/- `bind` combines two programs. If one of the program is just pure data (`some`), we can remove the bind. -/

/- Pure data as the first program (`some a`):

    do
      a' ← some a,
      f a'
    ═════════════
    f a
-/
lemma option.pure_bind {α β : Type} (a : α) (f : α → option β) :
  some a >>= f = f a :=
by refl
-- this is actually the definition of `option.bind` (i.e. `>>=`)

/- Pure data as the second program (`some a`):

    do
      a ← x,
      some a
    ══════════════
    x
-/
lemma option.bind_pure {α β : Type} : ∀x : option α, x >>= some = x
| none     := by refl
| (some a) := by refl

/- Nested programs `x`, `f`, `g` can be linearized using this associativity rule:

    do
      b ← (do
        a ← x,
        f a),
      g b
    ══════════
    do
      a ← x,
      b ← f a,
      g b
-/
lemma option.bind_assoc {α β γ : Type} {f : α → option β} {g : β → option γ} :
  ∀x : option α, (x >>= f) >>= g = x >>= (λa, f a >>= g)
| none     := by refl
| (some a) := by refl

end problem


/- The monad abstraction -/

class monad (M : Type → Type) extends has_bind M, has_pure M : Type 1 :=
-- law 1: left unit
(pure_bind {α β} (a : α) (f : α → M β) :
  pure a >>= f = f a)
-- law 2: right unit
(bind_pure {α} (m : M α) :
  m >>= pure = m)
-- law 3: associativity
(bind_assoc {α β γ} (f : α → M β) (g : β → M γ) (m : M α) :
  ((m >>= f) >>= g) = (m >>= (λa, f a >>= g)))

attribute [simp] lecture.monad.bind_pure lecture.monad.bind_assoc lecture.monad.pure_bind

open lecture.monad

-- Lean's monads look slightly different, due to separation of syntax and semantics (laws)
#print _root_.monad
#print _root_.is_lawful_monad


/- Part 2: Instances and application -/

/- The option monad: representing failure and partiality -/

namespace option

def pure {α : Type} : α → option α := option.some

def bind {α β : Type} : option α → (α → option β) → option β
| none     f := none
| (some a) f := f a

instance : monad option :=
{ pure       := @option.pure,
  bind       := @option.bind,
  pure_bind  := assume α β a f, by refl,
  bind_pure  := assume α m, match m with none := by refl | some a := by refl end,
  bind_assoc := assume α β γ f g m, match m with none := by refl | some a := by refl end }

end option


/- The state monad: representing an imperative state -/

def state (σ : Type) (α : Type) := σ → α × σ

namespace state

variable {σ : Type}

def get : state σ σ
| s := (s, s)

def set (s : σ) : state σ unit
| t := ((), s)

def bind {α β : Type} (f : state σ α) (g : α → state σ β) : state σ β
| s := function.uncurry g (f s)

def pure {α : Type} (a : α) : state σ α
| s := (a, s)

/- Example: remove all elements which are smaller than a previous elements in the list. -/
def diff_list : list ℕ → state ℕ (list ℕ)
| []       := pure []
| (x :: l) := do
  prev ← get,
  if x < prev then
    do
      diff_list l
  else
    do
      set x,
      l' ← diff_list l,
      pure (x :: l')

/- To execute `diff_list` we need to provide a start state, we also get back the last state (i.e. the
largest element) -/
#eval diff_list [1, 2, 3, 2]  0
#eval diff_list [1, 2, 3, 2, 4, 5, 2]  0

instance : monad (state σ) :=
{ pure       := @state.pure σ,
  bind       := @state.bind σ,
  pure_bind  := assume α β a f, funext $ assume s, by refl,
  bind_pure  := assume α m, funext $ assume s,
  begin
    simp [bind],
    cases (m s),
    refl
  end,
  bind_assoc := assume α β γ f g m, funext $ assume s,
  begin
    simp [bind],
    cases (m s),
    refl
  end }

end state


/- Concrete monadic programs: adding custom operations -/

namespace interaction_example

section

parameters
  {M : Type → Type}
  [monad M]
  (write : string → M unit)
  (read : M string)

example : M bool := do
  write "Enter a truth value:",
  n ← read,
  if n = "true"
    then do write "true", pure tt
    else do write "false", pure ff

def combine_v1 : M string := do
  write "Part 1:",
  p₁ ← read,
  write "Part 2:",
  p₂ ← read,
  write ("Combined: " ++ p₁ ++ p₂),
  pure (p₁ ++ p₂)

def ask (msg : string) : M string := do
  write msg,
  r ← read,
  pure r

def combine_v2 : M string := do
  p₁ ← ask "Part 1:",
  p₂ ← ask "Part 2:",
  write ("Combined: " ++ p₁ ++ p₂),
  pure (p₁ ++ p₂)

set_option pp.binder_types false

-- Example: show equality between basic monadic programs
example : combine_v2 = combine_v1 :=
by simp [combine_v2, combine_v1, ask]

end

end interaction_example


/- `mmap`: iterating over a list -/

section mmap

variables {M : Type → Type} [monad M] {α β γ δ : Type}

def mmap (f : α → M β) : list α → M (list β)
| []       := pure []
| (a :: l) := do
  b ← f a,
  l' ← mmap l,
  pure (b :: l')

lemma mmap_append (f : α → M β) :
  ∀(l l' : list α),
    mmap f (l ++ l') = do
      xs ← mmap f l,
      ys ← mmap f l',
      pure (xs ++ ys)
| []       l' := by simp [mmap]
| (a :: l) l' := by simp [mmap, mmap_append l l']

/- `nths l n` selects the `(n + 1)`st elements of each list in `l`.
It fails if not all lists are long enough. Intuitively:

    nths [[x00, x01, …],
          [x10, x11, …],
             ⋮    ⋮
          [xN0, xn2, …]] 3 = [x03, x13, …, xN3]

The lists [xI0, xI1, …] may have different length (but they are all finite). -/

def nths {α : Type} (l : list (list α)) (n : ℕ) : option (list α) :=
mmap (λl, list.nth l n) l

end mmap

end lecture
