/- Exercise 2.1: Functional Programming — Lists -/

/- Question 1: Counting elements -/

/- 1.1. Define a function `count` that counts the number of occurrences of an element in a list. It
should be similar to `bcount` from the lecture, except that it takes a value `α` instead of a
predicate `α → bool`.

`decidable_eq` is the type class of types whose equality is decidable. -/

def count {α : Type} (a : α) [decidable_eq α] : list α → ℕ
| [] := 0
| (x :: xs) := count xs + 1



/- 1.2. Test your definition of `count` on a few examples to convince yourself that it is
correct. This is something you should always do regardless of whether we ask for it.

You can use `#reduce` or (if `#reduce` fails) `#eval` to do this. -/

#reduce count "a" ["a", "a"] 
#reduce count 2 [2,2,2,2,2]
#reduce count 0 [0,0,0,0]

/- 1.3. Complete the following proof (or replace it with a new proof structure of your own).

Hints: Some of the following lemmas might be useful to reason about `≤`. Moreover, if it helps you
carry out the proof, you could reconsider revising your answer to question 1.1. -/

#check nat.le_add_left
#check nat.le_add_right
#check add_le_add_left
#check add_le_add_right

lemma count_le_length {α : Type} (a : α) [decidable_eq α] :
  ∀xs : list α, count a xs ≤ list.length xs
| [] := by refl
| (x :: xs) :=
  calc count a (x :: xs) = count a xs + (if x = a then 1 else 0) :
    begin repeat{simp[count]}, induction xs, simp[count],  end
  ... ≤ list.length xs + (if x = a then 1 else 0) :
    sorry
  ... ≤ list.length (x :: xs) :
    begin repeat{simp[count]}, simp[count_le_length a] end


/- Question 2: Removing duplicates -/

/- 2.1. Define a predicate `mem x xs` that returns true if `x` is an element of `xs`. -/

-- enter your answer here

/- The above `mem` predicate is not quite as convenient as the predefined `list.mem`, for which
theorems and a nice notation (infix `∈`) are available, including a proof of decidability. Let's use
`list.mem` from now on.  -/

#print list.has_mem
#check list.mem
#check list.decidable_mem

/- 2.2. Define a function `remdups` that removes duplicate elements in a list. For example,
`remdups [1, 2, 1, 3]` could return either `[1, 2, 3]` or `[2, 1, 3]`, depending of which of the two
occurrences of `1` is kept.

Hint: One of the two behaviors is easier to implement. -/

-- enter your answer here

/- 2.3. Test your implementation on more than two input values, using `#reduce` or `#eval`, and put
the expected value in a comment. -/

-- enter your answer here

/- Do you find yourself copy-pasting the outcome of `#reduce` into the comment? If so, this defeats
the point of writing a test. You should first think for yourself of the expected result, write it
down, and then compare the actual result with it. -/

/- 2.4. Define a function `remdups_adj` that compresses adjacent duplicates. For example, it would
leave `[1, 2, 1, 3]` unchanged but compress `[1, 1, 2, 2, 2, 1, 3, 3]` to `[1, 2, 1, 3]`. -/

-- enter your definition here

/- 2.5. Test your implementation on the same values as you used for question 2.3. -/

-- enter your answer here

/- Do the tests detect any difference in behavior between `remdups` and `remdups_adj`? If the answer
is no, this is a strong indication that your tests were incomplete to start with. -/

/- 2.6. Prove that `remdups` does not influence the behavior of `list.mem`.

Hint: Use `by_cases` to distinguish between the case where a given element is kept and the case
where it is removed. -/

@[simp] lemma mem_remdups {α : Type} (a : α) [decidable_eq α] :
  ∀xs : list α, a ∈ remdups xs ↔ a ∈ xs
:= sorry

/- 2.7. State and prove that `remdups_adj` does not influence the behavior of `list.mem`. -/

-- enter your answer here

/- 2.8. State and prove that `remdups` is idempotent (i.e., that applying it twice has the same
effect as applying it only once). -/

-- enter your answer here

/- 2.9 (**optional bonus**). State and prove that `remdups_adj` is idempotent.

Warning: This one is difficult. -/

-- enter your answer here
