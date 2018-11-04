/- Question 2: Map -/

/- 2.1. Define a generic `map` function that applies a function to every
   element in a list. -/

def map {α : Type} {β : Type} (f : α → β) : list α → list β
| [] := []
| (a::b) := (f a) :: (map b)

#reduce map(+10)[2,4,5]
#reduce map(/2)[10,20,30]