/- Homework 2.2: Functional Programming — Trees -/

/- Question 1: Huffman's algorithm -/

/- Recall the following definition from the lecture. -/

inductive tree (α : Type)
| leaf : ℕ → α → tree
| inner : ℕ → tree → tree → tree

export tree (leaf inner)

/- To make our lives easy, we will fix a type α of symbols equipped with decidable equality
throughout this question. -/

section

parameter (α : Type)
parameter [decidable_eq α]

/- We start by defining the alphabet of a tree: the set of its labels. We use lists to represent
sets to get executability for free. The cost is that we must ignore the order or number of
occurrences of elements in a list when comparing alphabets. -/

def alphabet : tree α → list α
| (leaf _ a)    := [a]
| (inner _ l r) := alphabet l ++ alphabet r

/- 1.1. Define the following function, so that we can obtain the alphabet of an entire forest
(i.e. list of trees).

Hint: Through this exercise, try to keep your definitions as simple as possible, because this will
affect proving ease further down. -/

def alphabet_list : list (tree α) → list α
| [] := []
| (x :: xs) := alphabet_list xs ++ alphabet x


/- A tree is consistent if it contains no duplicate labels. This can be defined as an inductive
predicate. -/

inductive consistent : tree α → Prop
| consistent_leaf (w : ℕ) (a : α) : consistent (leaf w a)
| consistent_inner (w : ℕ) (l : tree α) (r : tree α) :
  consistent l → consistent r → (∀a, a ∈ alphabet l → a ∈ alphabet r → false) →
  consistent (inner w l r)

/- 1.2. A forest is consistent if it contains no duplicate labels (even in different trees). Define
an inductive predicate `consistent_list` that captures this property. -/

inductive consistent_trees : list (tree α) → Prop
| consistent_leaf (w : ℕ) (a: list (tree α )) : consistent_trees a
| consistent_inner (w : ℕ) (l : list (tree α)) (r : list(tree α)) :
  consistent_trees l → consistent_trees r → (∀a, a ∈ alphabet_list l → a ∈ alphabet_list r → false) →
  consistent_trees r

/- 1.3. The height of a tree is the length of the longest path from its root node to a leaf. A tree
consisting of a single node has height 0 by convention. Define a recursive function `height` that
computes this.

Hint: You may use the built-in `max` function. -/

def height {α: Type} : tree α → ℕ
| (leaf _ a) := 1
| (inner _ l r) := 1 + max (height l) (height r)


/- 1.4. Now define the same function on forests, where the height of a forest is defined as the
height of its tallest tree. -/

def height_forest {α: Type}: list(tree α) → ℕ 
| [] := 0
| (x :: xs) :=  1 + max (height x) (height_forest xs)


/- 1.5. Define a function that returns the depth of a symbol in a tree. For example, if the symbol
is stored in a leaf node immediately below the root, it would be at depth 1. Symbols that do not
occur in the tree are conventionally put at depth 0. For symbols that occur several times as labels,
you can arbitrarily choose which occurrence to consider (e.g. the leftmost one). -/

def depth : tree α → α → ℕ
| (leaf _ a) x := 1
| (inner _ l r) x := 0

/- 1.6. State and prove that the depth of a symbol in a tree is less than or equal to the height of
the tree.



Hint: You might find the lemmas `le_max_left`, `add_le_add_left`, and similarly named ones useful.
Use Visual Studio Code's Command Palette to explore Lean's library (e.g. `#le_max`). -/
lemma depthlessequal {α: Type} (a: α) : depth (tree a) ≤ height (tree)

/- 1.7. A tree's height is not only an upper bound on the depth of symbols stored in the tree. It is
also a tight bound. Complete the following proof. -/

lemma exists_at_height : ∀t : tree α, consistent t → ∃a ∈ alphabet t, depth t a = height t
| (leaf _ a)      ct :=
  begin
    repeat {apply exists.intro},
    simp[alphabet],
    simp[depth, height]
  end
| t@(inner _ l r) ct :=  -- `t@` introduces the alias `t` for `inner _ l r`
  have cl : consistent l :=
   begin
    have bla: ∀ (t : tree α), consistent t → (∃ (a : α) (H : a ∈ alphabet t), depth t a = height t) ,
    intro a,
    intro b,
    repeat{apply exists.intro},


   end
  have cr : consistent r :=
   sorry,
  let ⟨b, b_in_alpha_l, depth_l_b_eq_height_l⟩ := exists_at_height l cl in
  let ⟨c, c_in_alpha_r, depth_r_c_eq_height_r⟩ := exists_at_height r cr in
  let b_or_c := if height r ≤ height l then b else c in
  have borc_in_alpha_t : b_or_c ∈ alphabet t :=
   begin
    repeat {apply exists.intro},
    simp[alphabet],
    apply or.inr,
    show b_or_c ∈ alphabet r, from c_in_alpha_r 
    
    
   end
  have depth_t_borc_eq_height_t : depth t b_or_c = height t :=
   sorry,  -- **optional**
  ⟨b_or_c, borc_in_alpha_t, depth_t_borc_eq_height_t⟩

end


/- Question 2: Enter your question here. -/
