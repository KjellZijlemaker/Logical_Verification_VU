inductive tc1 {α: Type} (r: α → α → Prop) : α → α → Prop
| base : ∀a b, r a b → tc1 a b
| step : ∀a b c, r a b → tc1 b c → tc1 a c

inductive tc2 {α: Type} (r: α → α → Prop) : α → α → Prop
| base : ∀a b, r a b → tc2 a b
| pets : ∀a b c, r a b → r b c → tc2 a c 


inductive tc3 {α: Type} (r: α → α → Prop) : α → α → Prop
| base : ∀a b, r a b → tc3 a b
| trans : ∀a b c, tc3 a b → tc3 b c → tc3 a c 


lemma tc3_step {α: Type} (r : α → α → Prop) :
∀ a b c : α, r a b → tc3 r b c → tc3 r a c :=
begin
intros a b c,
intros l1 l2,
apply tc3.trans a b,
apply tc3.base,
assumption,
assumption
end

lemma tc1_pets {α: Type} (r: α → α → Prop) :
∀ a b c : α, tc1 r a b → r b c → tc1 r a c :=
begin
intros a b c,
intro rab,
intro rbc,
apply tc1.step a b,

end


def mem {α: Type} (a: α) : list α → Prop
| [] := false
| (x::xs) := x = a ∨ mem xs

def reverse {α: Type}: list α → list α
| [] := []
| (x :: xs) := reverse xs ++ [x]

def count  {α: Type} (a: α) [decidable_eq α]: list α → ℕ
| [] := 0
| (x :: xs) := if x = a then 1 + count xs else count xs 

lemma count_eq_zero_iff_not_mem {α: Type} (a: α)[decidable_eq α] :
∀xs, count a xs = 0 ↔ ¬ mem a xs
| [] := by simp[count, mem]
| (x :: xs) := begin apply iff.intro, intro c, simp[mem], intro f, simp[count] at c, cases f,  end


lemma count_reverse_eq_count {α: Type} (a: α) [decidable_eq α]:
∀xs : list α, count a (reverse xs) = count a xs
| [] := by simp[count, reverse]
| (x :: xs) := begin simp[count],simp[reverse],  end 


inductive wl (σ: Type) : Type
| skip {}   : wl
| assign    : (σ → σ) → wl
| seq       : wl → wl → wl
| ite       : (σ → Prop) → wl → wl → wl
| while     : (σ → Prop) → wl → wl

inductive dl (σ: Type) : Type
| skip {}   : dl
| assign    : (σ → σ) → dl
| seq       : dl → dl → dl
| unless    : dl → (σ → Prop) → dl 
| do_while  : dl → (σ → Prop) → dl 


def wl_of_dl (σ: Type) : dl σ → wl σ
| dl.skip   := wl.skip
| dl := wl


def double : ℕ → ℕ := λ x, x + x
def square : ℕ → ℕ := λ x, x * x
def do_twice : (ℕ → ℕ) → ℕ → ℕ := λ f x, f (f x)

def Do_Twice : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ) := λ f g x, f g x

#reduce Do_Twice do_twice double 9


-- def curry (α β γ : Type) (f : α × β → γ) : α → β → γ := λ a b, b 

constants p q : Prop

theorem t1 : p → q → p :=
begin
intros s a,

end


variables p q : Prop
variables  (hp : p) (hq : q)

lemma test : (p ∧ q) ↔ (q ∧ p) := 
begin 
    apply iff.intro,
    intro pq,
    apply and.intro,
    apply and.elim_right pq,
    apply and.elim_left pq,
    intro qp,
    apply and.intro,
    apply and.elim_right qp,
    apply and.elim_left qp
end