def new_list_sizeof : has_sizeof (list ℕ) := ⟨list.length⟩
local attribute [instance, priority 100000] new_list_sizeof

-- def insert {α: Type} (i: Prop) [decidable i] :list α → list α
-- | [] := [i]
-- | (x :: xs) := if x >= i then i :: (x :: xs) else x :: insert i xs

-- -- def insertionSort {α: Type}: list α → ℕ → list α
-- -- | [] 0 := []
-- -- | (x :: xs) n := 


-- Creating definitions for the mergesort
def fhalf {α: Type} (xs: list α): list α := list.take (list.length xs/2) xs

def sndhalf {α: Type} (xs: list α): list α := list.drop (list.length xs/2) xs

#reduce fhalf [1,2,3,4,5, 6]
#reduce sndhalf [1,2,3,4,5,6]


-- Definition of the merge (sorting all in one go)
def merge : list ℕ → list ℕ → list ℕ
   | xs [] := xs
   | [] ys := ys
   | (x :: xs) (y :: ys) := if x < y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys

-- Standard definitions for proving with merge later
def reverse {α : Type} : list α → list α
| []        := []
| (x :: xs) := reverse xs ++ [x]

def concat {α: Type}: list (list α) → list α
| [] := []
| (xs :: xss) := xs ++ concat xss

      -- then x :: y :: merge xs ys

-- Testing the merge
#reduce merge [2,23,1] [22,6,7]    --Expecting: [2, 2, 3, 3, 4, 7]
#reduce merge [22,6,7] [2,23,1]     --Expecting: [2, 2, 3, 3, 4, 7]
#reduce merge [2,3,4] [2,3,7]    --Expecting: [2, 2, 3, 3, 4, 7]


#reduce reverse(reverse(merge [2,3,7] [2,3,4]))

-- def mergepairs : list(list ℕ) → list(list ℕ)
-- | (xs :: xss :: xsss) := merge xs xss :: mergepairs xsss
-- | xsss := xsss

-- def merge' : list(list ℕ) → list(list ℕ) 
-- | [] := []
-- | [x] := [x]
-- | xs := merge' (mergepairs xs)




def mergesort : list ℕ → list ℕ 
   | [] := []
   | [a] := [a]
   | (xs) := 
      have list.sizeof (fhalf xs) < list.sizeof xs, from begin simp[fhalf], cases xs, simp,  end,
      have list.sizeof (sndhalf xs) < list.sizeof xs, from begin simp[sndhalf], simp [fhalf]  at this, cases xs, simp, simp[] end,
   merge (mergesort (fhalf xs)) (mergesort (sndhalf xs))

-- def mergesortt : list ℕ → list ℕ     
-- | [] := []    
-- | [a] := [a]  
-- | (x::xs) := 
--   have list.sizeof (fhalf xs) < x + (1 + list.sizeof xs), from begin induction x, simp, simp[fhalf], cases xs, simp, assumption end,
--   have list.sizeof (sndhalf xs) < x + (1 + list.sizeof xs), from sorry,
--   merge (mergesort (fhalf xs)) (mergesort (sndhalf xs))

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
| (x :: xs) (xx :: xss) := begin  intro x2, simp[merge], simp[merge_cons], sorry end

lemma comm_merge : ∀(n m: list ℕ), merge m n = merge n m 
| [] xs :=  by simp[nil_merge, merge_nil]
| (x :: xs) xss := by simp[merge_cons]


