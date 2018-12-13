def concat {α : Type} : list (list α) → list α 
| [] := [] 
| (xs :: xss) := xs ++ concat xss

def map {α β : Type} (f : α → β) : list α → list β |
 [] := [] |
  (x :: xs) := f x :: map xs

lemma map_concat {α β : Type} (f : α → β) : ∀xss : list (list α), map f (concat xss) = concat (map (map f) xss)
| [] := by refl
| (xs :: xss) := begin rw[concat], rw[map], rw[concat], rw[<-map_concat xss], end

def reverseList {α: Type}: list α → list α
| [] := []
| (x::xs) := reverseList xs ++ [x]


#reduce reverseList [2,3,4,5]
-- intro xss,
-- induction xss,
-- refl,
-- simp[map],
-- simp[concat],
-- rw[<-xss_ih],

