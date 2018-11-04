/- Homework 1.1: Basics — Specifications -/

/- Question 1: Snoc -/

/- 1.1. Define the function `snoc` that appends a single element to the end of
   a list. -/

def snoc {α : Type} : list α → α → list α
| [] l := [] ++ [l]
| (a::b) l := a :: b ++ [l]

#reduce snoc [] 5
#reduce snoc [2,4,6] 8

/- 1.2. Convince yourself that your definition of `snoc` works by testing it on
   a few examples. -/

-- invoke `#reduce` here


/- Question 2: Map -/

/- 2.1. Define a generic `map` function that applies a function to every
   element in a list. -/

def map {α : Type} {β : Type} (f : α → β) : list α → list β
| [] := []
| (a::b) := (f a) :: (map b)

#reduce map(+10)[2,4,5]
#reduce map(/2)[10,20,30]

/- 2.2. State the so-called functiorial properties of `map` as lemmas.
   Schematically:

     map (λx, x) xs = xs
     map (λx, g (f x)) xs = map g (map f xs)

   Make sure to state the second law as generally as possible, for
   arbitrary types.
-/

-- enter your lemma statements here
