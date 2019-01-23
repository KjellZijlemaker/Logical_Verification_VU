/- Exercise 1.1: Basics — Specifications -/

/- Replace the placeholders (e.g. `:= sorry`) with your solutions. -/


/- Question 1: Fibonacci numbers -/

/- 1.1. Define the function `fib` that returns the Fibonacci numbers. -/

def fib : ℕ  → ℕ  
| 0 := 0 
| 1 := 1 
| (n+2) := fib (n+1) + fib n

/- 1.2. Check that your function works as expected. -/

#reduce fib 0  -- expected: 0
#reduce fib 1  -- expected: 1
#reduce fib 2  -- expected: 1
#reduce fib 3  -- expected: 2
#reduce fib 4  -- expected: 3
#reduce fib 5  -- expected: 5
#reduce fib 6  -- expected: 8


/- Question 2: Arithmetic Expressions -/

/- 2.1: Define an inductive type `aexp` to represent arithmetic expressions.
   It should be equipped with six constructors:

   * `num` takes an integer (ℤ = \int) and represents that integer;
   * `var` takes a string and represents a variable of that name;
   * `add`, `sub`, `mul`, `div` take two arithmetic expressions and represent
     the operations +, -, *, and /, respectively.
-/

inductive aexp
| num : ℤ → aexp
| var : string  → aexp
| add : aexp → aexp → aexp
| sub : aexp → aexp → aexp
| mul : aexp → aexp → aexp
| div: aexp → aexp → aexp  



/- 2.2: Define an evaluation function `eval` that takes an environment, giving
   the value of variables, and an arithmetic expression and that returns an
   integer. -/


def eval (env : string → ℤ) : aexp → ℤ
| (aexp.num i) := i
| (aexp.var j) := env(j)
| (aexp.add m n):= eval(m) + eval(n)
| (aexp.sub m n):= eval(m) + eval(n)
| (aexp.div m n):= (eval m) + (eval n)
| (aexp.mul m n):= eval(m) + eval (n)

/- 2.3: Test `eval` on some examples, making sure to exercise each constructor
   at least once. You can use the following environment in your tests. -/

def some_env : string → ℤ
| "x" := 3
| "y" := 17
| _ := 201
ite_


-- invoke `#reduce` here
#reduce eval some_env(aexp.num(42))
#reduce eval some_env(aexp.add (aexp.num 4) (aexp.num 9))