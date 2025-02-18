import tuto_lib


section
/-
The first part of this file makes sure you can negate quantified statements
in your head without the help of `push_neg`.

You need to complete the statement and then use the `check_me` tactic
to check your answer. This tactic exists only for those exercises,
it mostly calls `push_neg` and then cleans up a bit.

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε
-/

-- In this section, u denotes a sequence of real numbers
-- f is a function from ℝ to ℝ
-- x₀ and l are real numbers
variables (u : ℕ → ℝ) (f : ℝ → ℝ) (x₀ l : ℝ)

/- Negation of "u tends to l" -/
-- 0062
example : ¬ (∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε) ↔
∃ ε > 0, ∀ N, ∃ n ≥ N, |u n - l| > ε
:=
begin
  check_me,
end

/- Negation of "f is continuous at x₀" -/
-- 0063
example : ¬ (∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ →  |f x - f x₀| ≤ ε) ↔
∃ ε > 0, ∀ δ > 0, ∃ x, |x - x₀| ≤ δ ∧ |f x - f x₀| > ε
:=
begin
  check_me,
end

/-
In the next exercise, we need to keep in mind that
`∀ x x', ...` is the abbreviation of
`∀ x, ∀ x', ... `. 

Also, `∃ x x', ...` is the abbreviation of `∃ x, ∃ x', ...`.
-/

/- Negation of "f is uniformly continuous on ℝ" -/
-- 0064
example : ¬ (∀ ε > 0, ∃ δ > 0, ∀ x x', |x' - x| ≤ δ →  |f x' - f x| ≤ ε) ↔
∃ ε > 0, ∀ δ > 0, ∃ x x', |x' - x| ≤ δ ∧ |f x' - f x| > ε
:=
begin
  check_me,
end

/- Negation of "f is sequentially continuous at x₀" -/
-- 0065
example : ¬ (∀ u : ℕ → ℝ, (∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - x₀| ≤ ε) → (∀ ε > 0, ∃ N, ∀ n ≥ N, |(f ∘ u) n - f x₀| ≤ ε))  ↔
(∃ u : ℕ → ℝ, (∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - x₀| ≤ ε) ∧  (∃ ε > 0, ∀ N, ∃ n ≥ N, |(f ∘ u) n - f x₀| > ε))
:=
begin
  check_me,
end
end

/-
We now turn to elementary applications of negations to limits of sequences.
Remember that `linarith` can find easy numerical contradictions.

Also recall the following lemmas:

abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y

ge_max_iff (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q

le_max_left p q : p ≤ max p q

le_max_right p q : q ≤ max p q

/-- The sequence `u` tends to `+∞`. -/
def tendsto_infinity (u : ℕ → ℝ) := ∀ A, ∃ N, ∀ n ≥ N, u n ≥ A
-/

-- 0066
example {u : ℕ → ℝ} : tendsto_infinity u → ∀ l, ¬ seq_limit u l :=
begin
  intros inf l lim,
  cases lim 1 (by linarith) with N hN,
  cases inf (l + 2) with N' hN',
  have := hN (max N N') (by apply le_max_left),
  rw abs_le at this,
  have k: u (max N N') ≤ l + 1, by linarith,
  have k':= hN' (max N N') (by apply le_max_right),
  by linarith,
end

def nondecreasing_seq (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

-- 0067
example (u : ℕ → ℝ) (l : ℝ) (h : seq_limit u l) (h' : nondecreasing_seq u) :
  ∀ n, u n ≤ l :=
begin
  by_contra' hyp,
  cases hyp with n0 un0,
  cases h ((u n0-l)/2) (by linarith) with N hN,
  have k := hN (max n0 N) (by apply le_max_right),
  rw abs_le at k,
  have :=
    calc u n0 ≤ u (max n0 N): by linarith[h' n0 (max n0 N) (le_max_left n0 N) ]
          ... ≤ l + ((u n0-l)/2): by linarith
          ... < u n0: by linarith,
  by linarith,
end

/-
In the following exercises, `A : set ℝ` means that A is a set of real numbers.
We can use the usual notation x ∈ A.

The notation `∀ x ∈ A, ...` is the abbreviation of `∀ x, x ∈ A → ... `

The notation `∃ x ∈ A, ...` is the abbreviation of `∃ x, x ∈ A ∧ ... `.
More precisely it is the abbreviation of `∃ x (H : x ∈ A), ...`
which is Lean's strange way of saying `∃ x, x ∈ A ∧ ... `. 
You can convert between these forms using the lemma 
  exists_prop {p q : Prop} : (∃ (h : p), q) ↔ p ∧ q

We'll work with upper bounds and supremums.
Again we'll introduce specialized definitions for the sake of exercises, but mathlib
has more general versions.


def upper_bound (A : set ℝ) (x : ℝ) := ∀ a ∈ A, a ≤ x

def is_sup (A : set ℝ) (x : ℝ) := upper_bound A x ∧ ∀ y, upper_bound A y → x ≤ y


Remark: one can easily show that a set of real numbers has at most one sup,
but we won't need this.
-/

-- 0068
example {A : set ℝ} {x : ℝ} (hx : is_sup A x) :
∀ y, y < x → ∃ a ∈ A, y < a :=
begin
  intros y yx,
  by_contra' hyp,
  have : upper_bound A y, from hyp,
  have k := hx.2 y this,
  by linarith,
end

/-
Let's do a variation on an example from file 07 that will be useful in the last
exercise below.
-/

-- 0069
lemma le_of_le_add_all' {x y : ℝ} :
  (∀ ε > 0, y ≤ x + ε) →  y ≤ x :=
begin
  intros h,
  by_contra' xy,
  have k := h ((y-x)/2) (by linarith),
  by linarith,
end

-- 0070
example {x y : ℝ} {u : ℕ → ℝ} (hu : seq_limit u x)
  (ineg : ∀ n, u n ≤ y) : x ≤ y :=
begin
  by_contra' yx,
  cases hu ((x-y)/2) (by linarith) with N hN,
  specialize hN N (by linarith),
  specialize ineg N,
  rw abs_le at hN,
  by linarith,
end

