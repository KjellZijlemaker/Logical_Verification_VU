def new_list_sizeof : has_sizeof (list ℕ) := ⟨list.length⟩
local attribute [instance, priority 100000] new_list_sizeof

-- Creating definitions for the mergesort
def fhalf {α: Type} (xs: list α): list α := list.take (list.length xs/2) xs
def sndhalf {α: Type} (xs: list α): list α := list.drop (list.length xs/2) xs

#reduce fhalf [1,2,3,4,5,6]     --Expecting [1, 2, 3]
#reduce sndhalf [1,2,3,4,5,6]   --Expecting [4, 5, 6]


-- Definition of the merge (merging two lists with the smallest first)
def merge : list ℕ → list ℕ → list ℕ
   | xs [] := xs
   | [] ys := ys
   | (x :: xs) (y :: ys) := if x < y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys

-- Standard definitions for proving with merge later
def reverse {α : Type} : list α → list α
| []        := []
| (x :: xs) := reverse xs ++ [x]

-- Testing the merge
#reduce merge [8, 2, 1] [2,1,4]  --Expecting: [2, 1, 4, 8, 2, 1]
#reduce merge [2,3,4] [2,3,7]    --Expecting: [2, 2, 3, 3, 4, 7]


#reduce reverse(reverse(merge [2,3,7] [2,3,4]))

lemma test : 1 < 1 + 1 := sorry

def mergesort : list ℕ → list ℕ     
| [] := []    
| [a] := [a]  
| (x::xs) := 
  have list.sizeof (fhalf xs) < x + (1 + list.sizeof xs), from begin induction x, simp, simp[fhalf], cases xs, simp, simp[list.sizeof], simp[test],simp[list.sizeof] end,
  have list.sizeof (sndhalf xs) < x + (1 + list.sizeof xs), from sorry,
  merge (mergesort (fhalf xs)) (mergesort (sndhalf xs))

-- #reduce mergesort [10,2,1,2,3] 


-- Proving the merge definition instead of the mergesort as it includes the merge defenition. 

-- Proving the reverse definitions which will also partially be applied to the merge definition
lemma reverse_append {α : Type} :
  ∀xs ys : list α, reverse (xs ++ ys) = reverse ys ++ reverse xs
| [] ys := by simp[reverse]
| (x :: xs) ys := begin simp[reverse, reverse_append] end


lemma reverse_append_nil : ∀{α:Type} (xs:list α) (x:α), reverse (x::xs) = reverse xs ++ ( x :: list.nil) 
| xs [] := by simp[reverse]
| xs (x :: xss) := begin intro xsss, simp[reverse] end 

lemma reverse_reverse {α : Type} : ∀xs : list α, reverse (reverse xs) = xs
| [] := by simp[reverse]
| (x :: xs) := begin simp[reverse], simp[reverse_append], rw[reverse_reverse], rw[reverse], rw[reverse], refl  end


-- Proving merge properties
lemma merge_nil: ∀(n : list ℕ), merge ([] : list ℕ) n  = n
| [] := by refl
| (x :: xs) := by simp[merge]

lemma nil_merge: ∀(n : list ℕ), merge n ([] : list ℕ)  = n 
| [] := by refl
| (x :: xs) := by simp[merge]


lemma merge_reverse_reverse : ∀(n m: list ℕ), reverse(reverse(merge n m)) = merge n m 
| [] m := by simp[reverse_reverse]
| (x :: xs) m := by simp[reverse_reverse]

-- Seems obvious, but can't seem to prove the ite..
lemma merge_cons: ∀(xs xss : list ℕ), ∀(x: ℕ),  merge xs (x::xss) = merge (x::xss) xs 
| [] xss := by simp[merge]
| (x :: xs) [] := begin intro x2, simp[merge], simp[merge_cons], sorry end
| (x :: xs) (xx :: xss) := begin  intro x2, simp[merge], sorry end

lemma comm_merge : ∀(n m: list ℕ), merge m n = merge n m 
| [] xs :=  by simp[nil_merge, merge_nil]
| (x :: xs) xss := by simp[merge_cons]


