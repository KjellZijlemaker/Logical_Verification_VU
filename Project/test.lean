def concat {α : Type} : list (list α) → list α 
| [] := [] 
| (xs :: xss) := xs ++ concat xss

def map {α β : Type} (f : α → β) : list α → list β |
 [] := [] |
  (x :: xs) := f x :: map xs


def reverse {α: Type}: list α → list α
| [] := []
| (x::xs) := reverse xs ++ [x]


lemma concat_snoc {α : Type} : ∀(xs : list α) (xss : list (list α)), concat (xss ++ [xs]) = concat xss ++ xs:=sorry
lemma reverse_append {α : Type} : ∀xs ys : list α, reverse (xs ++ ys) = reverse xs ++ reverse ys := sorry

lemma reverse_concat {α : Type} : ∀xss : list (list α), reverse (concat xss) = concat (reverse (map reverse xss))
| [] := by refl
| (x :: xs) := begin simp[concat], simp[map], simp[reverse], simp[reverse_append], simp[concat_snoc], rw[reverse_concat xs]  end


inductive sorted: list ℕ → Prop
| nil : sorted []
| single {n: ℕ} : sorted [n]
| largertwo {x y: ℕ} {xs: list ℕ} (xy: x <= y) (yxs: sorted (y :: xs)) : sorted (x :: y :: xs)
-- intro xss,
-- induction xss,
-- refl,
-- simp[map],
-- simp[concat],
-- rw[<-xss_ih],

example : sorted [] := sorted.nil

example : sorted [2] := sorted.single

example : sorted [3, 5] := begin apply sorted.largertwo, trivial, sorted.single  end
example : sorted [7, 9, 9, 11] := begin apply repeat{sorted.largertwo}, trivial, end



inductive program (σ : Type) : Type 
| skip {} : program 
| assign : (σ → σ) → program 
| seq : program → program → program 
| ite : (σ → Prop) → program → program → program 
| while : (σ → Prop) → program → program

def program_equiv (p1 p2 : program σ) : Prop :=
 ∀s t, (p1, s) =⇒ t ↔ (p2, s) =⇒ t 


inductive finite {α: Type}: set α → Prop
| empty: finite ∅
| single {a: α}: finite(insert a ∅)
| both_fin {A B: set α} (fin_A: finite A) (fin_B: finite B): finite (A ∪ B)

lemma finite.union {α : Type} : ∀A B : set α, finite A → finite B → finite (A ∪ B) :=
begin
intros A B,
intros finA finB,
apply finite.both_fin,
assumption,
assumption
end

instance fin_set.rel (α : Type) : setoid (list α) := 
{ r := λxs ys, ∀x, x ∈ xs ↔ x ∈ ys,
 iseqv := r x x 
  }

lemma isreflective {α: Type} (xs: list α): xs = xs := sorry



 
namespace v1



def concat {α: Type}: list (list α) → list α
| [] := []
| (xs :: xss) := xs ++ concat xss

def reverse {α: Type}: list α → list α
| [] := []
| (x :: xs) := reverse xs ++ [x]

#reduce reverse [2,3,4]

def map {α β: Type} (f: α → β): list α → list β
| [] := []
| (x :: xs) := f x :: map xs

lemma map_append {α: Type}: ∀xs ys : list α, map f (xs ++ ys) = (map xs) ++ (map ys)
#reduce  map 2 [2,3,4]


lemma map_concat {α β : Type} (f : α → β) : ∀xss : list (list α), map f (concat xss) = concat (map (map f) xss)
| [] := by refl
| (x :: xss) := begin simp[concat], simp[map], simp[concat], rw[<-map_concat xss], induction xss, simp[concat], simp[map], simp[map_concat], simp[map], simp[concat],  end

lemma concat_snoc {α : Type} : ∀(xs : list α) (xss : list (list α)), concat (xss ++ [xs]) = concat xss ++ xs := sorry

lemma reverse_append {α : Type} : ∀xs ys : list α, reverse (xs ++ ys) = reverse xs ++ reverse ys := sorry

lemma reverse_concat {α : Type} : ∀xss : list (list α), reverse (concat xss) = concat (reverse (map reverse xss))
| [] := by refl
| (x :: xss) := begin simp[concat], simp[map], simp[reverse], simp[concat_snoc],simp[reverse_append], rw[reverse_concat xss], simp end

inductive sorted: list ℕ → Prop
| empty : sorted []
| any_list {a: ℕ}: sorted [a]
| greater_two {xs: list ℕ} {x y: ℕ} (xsmallery: x <= y) (sxy: sorted (y :: xs)) : sorted (x :: y :: xs)

example : sorted [] := sorted.empty
example : sorted [2] := sorted.any_list
example : sorted [3, 5] := begin apply sorted.greater_two, apply trivial, apply sorted.any_list end
example : sorted [7, 9, 9, 11] := begin apply sorted.greater_two, apply trivial, apply sorted.greater_two...end
example : ¬ sorted [17, 13] := begin assume s : sorted [17,13],begin have 17 <= 13 := match s with sorted.greater_two xy yxs := xy end end

-- inductive finite {α: Type} : set α → Prop
-- | empty : finite ∅
-- | finite_set {a: α} {A: set α} (finA : finite A) : finite ({a} ∪ A)

inductive finite {α: Type} : set α → Prop
| empty : finite ∅
| singleton {a: α} : finite (insert a ∅)
| ABFinite {finiteA finiteB: set α} (afinite: finite finiteA) (bfinite: finite finiteB) : finite (finiteA ∪ finiteB)

lemma finite.union {α : Type} :
∀A B : set α, finite A → finite B → finite (A ∪ B) :=
begin
intros A B,
intros finiteA finiteB,
apply finite.ABFinite,
repeat{assumption}
end


lemma refleciver {α: Type} (xs: list α): xs = xs := by refl

lemma symmetric {α: Type} (xs ys: list α): xs → ys = ys → xs := sorry

lemma transitive {α: Type} (xs ys zs: list α): xs → ys ∧ ys → zs = xs → zs := sorry
 
def fin_empty {α : Type} (a: α) : fin_set α := [[a]] 

end v1
