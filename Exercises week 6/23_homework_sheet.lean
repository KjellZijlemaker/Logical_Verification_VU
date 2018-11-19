/- Homework 2.3: Functional Programming — Monads -/

namespace homework


/- Question 1: `map` for monads

Define `map` for monads. This is the generalization of `map` on lists. Use the monad operations to
define `map`. The _functorial properties_ (`map_id` and `map_map`) are derived from the monad laws.

This time, we use Lean's monad definition. In combination, `monad` and `is_lawful_monad` include the
same constants, laws, and syntactic sugar as the `monad` type class from the lecture. -/

section map

variables {M : Type → Type} [monad M] [is_lawful_monad M]

/- 1.1. Define `map` on `M`.

**Hint:** The challenge is to find a way to create `M β`. Follow the types. -/

def map {α β} (f : α → β) (m : M α) : M β:=
do a ← m, 
   b ← f a,
   return b
/- 1.2. Prove the identity law for `map`. -/

lemma map_id {α} (m : M α) : map id m = m :=
sorry

/- 1.3. Prove the composition law for `map`. -/

lemma map_map {α β γ} (f : α → β) (g : β → γ) (m : M α) :
  map g (map f m) = map (g ∘ f) m :=
sorry

end map


/- Question 2: Monadic structure on lists -/

/- `list` can be seen as a monad, similar to `option` but with several possible outcomes. It is also
similar to `set`, but the results are ordered and finite. The code below sets `list` up as a
monad. -/

namespace list

protected def bind {α β : Type} : list α → (α → list β) → list β
| []       f := []
| (a :: l) f := f a ++ bind l f

protected def pure {α : Type} (a : α) : list α := [a]

lemma pure_eq_singleton {α} (a : α) : pure a = [a] :=
by refl

instance : monad list :=
{ pure := @list.pure,
  bind := @list.bind }

/- 2.1. Prove the following properties of `bind` under the empty list (`[]`), the list constructor
(`::`), and `++`. -/

@[simp] lemma bind_nil {α β} (f : α → list β) : [] >>= f = [] :=
sorry

@[simp] lemma bind_cons {α β} (f : α → list β) (a : α) (l : list α) :
  (a :: l) >>= f = f a ++ (l >>= f) :=
sorry

@[simp] lemma bind_append {α β} (f : α → list β) :
  ∀l l':list α, (l ++ l') >>= f = (l >>= f) ++ (l' >>= f)
:= sorry

/- 2.2. Prove the monadic laws for `list`.

**Hint:** The simplifier cannot see through the type class definition of `pure`. You can use
`pure_eq_singleton` to unfold the definition or `show` to state the lemma statement using `bind` and
`[...]`. -/

lemma pure_bind {α β} (a : α) (f : α → list β) : (pure a >>= f) = f a :=
sorry

lemma bind_pure {α} : ∀l : list α, l >>= pure = l
:= sorry

lemma bind_assoc {α β γ} (f : α → list β) (g : β → list γ) :
  ∀l : list α, (l >>= f) >>= g = l >>= (λa, f a >>= g)
:= sorry

lemma bind_pure_comp_eq_map {α β} {f : α → β} :
  ∀l : list α, l >>= (pure ∘ f) = list.map f l
:= sorry

/- 2.3 **optional**. Register `list` as a lawful monad. This may be a challenge. -/

instance : is_lawful_monad list :=
sorry

end list

end homework
