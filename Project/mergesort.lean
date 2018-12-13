

def insert {α: Type} (i: α) :list α → list α
| [] := [i]
| (x :: xs) := if x >= i then i :: (x :: xs) else x :: insert i xs

def insertionSort {α: Type}: list α → ℕ → list α
| [] 0 := []
| (x :: xs) n := 



def fhalf {α: Type} (xs: list α): list α := list.take (list.length xs/2) xs

def sndhalf {α: Type} (xs: list α): list α := list.drop (list.length xs/2) xs

#reduce fhalf [1,2,3,4,5, 6]
#reduce sndhalf [1,2,3,4,5,6]


def merge {α: Type}: list α → list α → list α
   | xs [] := xs
   | [] ys := ys
   | (x :: xs) (y :: ys) := x :: y :: merge xs ys
      
#reduce merge [2,3,7]  [2,3,4]


def mergesort {α: Type} (a: α): list α → list α
   | [] := []
   | [a] := [a]
   | (x::xs) :=  merge (mergesort (fhalf xs)) (mergesort (sndhalf xs)) 


#reduce mergesort [2,3,4,9,2,1]

lemma merge_nil {α : Type} : ∀(n : list α), merge ([] : list α) n  = n :=
begin
intro n,
cases n,
repeat {simp[merge]}
end

lemma merge_comm {α : Type} : ∀(n : list α),∀(a : list α), merge n a = merge a n :=
begin
intros a n,
induction a,
induction n,
simp[merge],
simp[merge],


end

lemma test {α : Type} : ∀(n : list α),∀(a : list α), merge (n ++ a) = merge (a ++ n) :=
begin
intros a n,
induction a,
simp[merge],
simp[merge],

end

section sort
 universe u
  parameters {α : Type u} (r : α → α → Prop) [decidable_rel r]
   local infix `=>` : 50 := r 
   def ordered_insert (a : α) : list α → list α 
   | [] := [a] 
   | (b :: l) := if a => b then a :: (b :: l) else b :: ordered_insert l 
   
   def insertion_sort : list α → list α 
   | [] := [] 
   | (b :: l) := ordered_insert b (insertion_sort l)

   def quicksort {α: Type} (a: α) : list α → list α
| [] := []
| (x :: xs) := if quicksort (list.filter < a, xs) then  ++ [x] else ++ quicksort (list.filter (>= x) xs)

end sort
