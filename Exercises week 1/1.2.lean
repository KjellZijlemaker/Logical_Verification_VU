/- Homework 1.1: Basics — Specifications -/

/- Question 1: Snoc -/

/- 1.1. Define the function `snoc` that appends a single element to the end of
   a list. -/

def snoc {α : Type} : list α → α → list α
| [] l := [] ++ [l]
| (a::b) l := a :: b ++ [l]

#reduce snoc [] 5
#reduce snoc [2,4,6] 8
#reduce snoc [9, 1, 2] 10