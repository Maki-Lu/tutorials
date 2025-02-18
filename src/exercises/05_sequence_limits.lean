import data.real.basic
import algebra.group.pi
import tuto_lib

notation `|`x`|` := abs x

/-
In this file we manipulate the elementary definition of limits of
sequences of real numbers. 
mathlib has a much more general definition of limits, but here
we want to practice using the logical operators and relations
covered in the previous files.

A sequence u is a function from ℕ to ℝ, hence Lean says
u : ℕ → ℝ
The definition we'll be using is:

-- Definition of « u tends to l »
def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

Note the use of `∀ ε > 0, ...` which is an abbreviation of
`∀ ε, ε > 0 → ... `

In particular, a statement like `h : ∀ ε > 0, ...`
can be specialized to a given ε₀ by
  `specialize h ε₀ hε₀`
where hε₀ is a proof of ε₀ > 0.

Also recall that, wherever Lean expects some proof term, we can
start a tactic mode proof using the keyword `by` (followed by curly braces
if you need more than one tactic invocation).
For instance, if the local context contains:

δ : ℝ
δ_pos : δ > 0
h : ∀ ε > 0, ...

then we can specialize h to the real number δ/2 using:
  `specialize h (δ/2) (by linarith)`
where `by linarith` will provide the proof of `δ/2 > 0` expected by Lean.

We'll take this opportunity to use two new tactics:

`norm_num` will perform numerical normalization on the goal and `norm_num at h` 
will do the same in assumption `h`. This will get rid of trivial calculations on numbers,
like replacing |l - l| by zero in the next exercise.

`congr'` will try to prove equalities between applications of functions by recursively 
proving the arguments are the same. 
For instance, if the goal is `f x + g y = f z + g t` then congr will replace it by
two goals: `x = z` and `y = t`.
You can limit the recursion depth by specifying a natural number after `congr'`. 
For instance, in the above example, `congr' 1` will give new goals
`f x = f z` and `g y = g t`, which only inspect arguments of the addition and not deeper.
-/

variables (u v w : ℕ → ℝ) (l l' : ℝ)

-- If u is constant with value l then u tends to l
-- 0033
example : (∀ n, u n = l) → seq_limit u l :=
begin
  intros h e he,
  use 1,
  intros n hn,
  specialize h n,
  rw h,
  norm_num,
  linarith,
end

/- When dealing with absolute values, we'll use lemmas:

abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y

abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|

abs_sub_comm (x y : ℝ) : |x - y| = |y - x|

You should probably write them down on a sheet of paper that you keep at 
hand since they are used in many exercises.
-/

-- Assume l > 0. Then u tends to l implies u n ≥ l/2 for large enough n
-- 0034
example (hl : l > 0) : seq_limit u l → ∃ N, ∀ n ≥ N, u n ≥ l/2 :=
begin
  intro h,
  specialize h (l/2) (by linarith),
  cases h with N p,
  use N,
  intros n hn,
  specialize p n hn,
  have: -(l/2) ≤ (u n-l) ∧ (u n-l) ≤ (l/2),
  {rwa ← abs_le,},
  linarith,
end

/- 
When dealing with max, you can use

ge_max_iff (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q

le_max_left p q : p ≤ max p q

le_max_right p q : q ≤ max p q

You should probably add them to the sheet of paper where you wrote 
the `abs` lemmas since they are used in many exercises.

Let's see an example.
-/

-- If u tends to l and v tends l' then u+v tends to l+l'
example (hu : seq_limit u l) (hv : seq_limit v l') :
seq_limit (u + v) (l + l') :=
begin
  intros ε ε_pos,
  cases hu (ε/2) (by linarith) with N₁ hN₁,
  cases hv (ε/2) (by linarith) with N₂ hN₂,
  use max N₁ N₂,
  intros n hn,
  cases ge_max_iff.mp hn with hn₁ hn₂,
  have fact₁ : |u n - l| ≤ ε/2,
    from hN₁ n (by linarith),  -- note the use of `from`.
                               -- This is an alias for `exact`, 
                               -- but reads nicer in this context 
  have fact₂ : |v n - l'| ≤ ε/2,
    from hN₂ n (by linarith), 
  calc
  |(u + v) n - (l + l')| = |u n + v n - (l + l')|   : rfl
                     ... = |(u n - l) + (v n - l')| : by congr' 1 ; ring
                     ... ≤ |u n - l| + |v n - l'|   : by apply abs_add
                     ... ≤  ε                       : by linarith,
end

/-
In the above proof, we used `have` to prepare facts for `linarith` consumption in the last line.
Since we have direct proof terms for them, we can feed them directly to `linarith` as in the next proof
of the same statement.
Another variation we introduce is rewriting using `ge_max_iff` and letting `linarith` handle the
conjunction, instead of creating two new assumptions.
-/

example (hu : seq_limit u l) (hv : seq_limit v l') :
seq_limit (u + v) (l + l') :=
begin
  intros ε ε_pos,
  cases hu (ε/2) (by linarith) with N₁ hN₁,
  cases hv (ε/2) (by linarith) with N₂ hN₂,
  use max N₁ N₂,
  intros n hn,
  rw ge_max_iff at hn,
  calc
  |(u + v) n - (l + l')| = |u n + v n - (l + l')|   : rfl
                     ... = |(u n - l) + (v n - l')| : by congr' 1 ; ring
                     ... ≤ |u n - l| + |v n - l'|   : by apply abs_add
                     ... ≤  ε                       : by linarith [hN₁ n (by linarith), hN₂ n (by linarith)],
end

/- Let's do something similar: the squeezing theorem. -/
-- 0035
example (hu : seq_limit u l) (hw : seq_limit w l)
(h : ∀ n, u n ≤ v n)
(h' : ∀ n, v n ≤ w n) : seq_limit v l :=
begin
  intros e e0,
  cases hu e e0 with N1 h1,
  cases hw e e0 with N2 h2,
  use max N1 N2,
  intros n hn,
  specialize h n,
  specialize h' n,
  rw ge_max_iff at hn,
  have k1: |u n - l| ≤ e, from h1 n (by linarith),
  have k2: |w n - l| ≤ e, from h2 n (by linarith),
  rw abs_le at k1, rw abs_le at k2,
  have k3: -e ≤ v n - l,
  {calc -e ≤ u n - l: k1.1
  ... ≤ v n - l: by linarith
  },
  have k4: v n - l ≤ e,
  {calc v n - l ≤ w n - l: by linarith
  ... ≤ e: k2.2,
  },
  rw abs_le,
  exact ⟨k3, k4⟩,
end

/- What about < ε? -/
-- 0036
example (u l) : seq_limit u l ↔
 ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε :=
begin
  split,
  {
    intros h e e0,
    cases h (e/2) (by linarith) with N Hn,
    use N,
    intros n hn,
    specialize Hn n hn,
    calc |u n - l| ≤ e/2: Hn
      ...  < e: by linarith,
  },
  {
    intros h e e0,
    cases h e (by linarith) with N Hn,
    use N,
    intros n hn,
    specialize Hn n hn,
    exact le_of_lt Hn,
  },
end

/- In the next exercise, we'll use

eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y
-/

-- A sequence admits at most one limit
-- 0037
example : seq_limit u l → seq_limit u l' → l = l' :=
begin
  intros p q,
  suffices: ∀ ε > 0, |l - l'| ≤ ε,
    from eq_of_abs_sub_le_all l l' this,
  intros e e0,
  cases p (e/2) (by linarith) with N1 h1,
  cases q (e/2) (by linarith) with N2 h2,
  have k1: |u (max N1 N2)-l| ≤ e/2, from h1 (max N1 N2) (le_max_left N1 N2),
  have k2: |u (max N1 N2)-l'| ≤ e/2, from h2 (max N1 N2) (le_max_right N1 N2),
  have k3: | l - u (max N1 N2) |=|  u (max N1 N2) - l |, by apply abs_sub_comm,
  calc | l-l' | = | (u (max N1 N2)-l') + (l - u (max N1 N2)) |: by congr' 1 ; ring
  ... ≤ | (u (max N1 N2)-l' ) | + | l - u (max N1 N2) |: by apply abs_add
  ... = | (u (max N1 N2)-l' ) | + | u (max N1 N2) - l |: by linarith
  ... ≤ e/2+e/2: add_le_add k2 k1
  ... = e: by ring,
end

/-
Let's now practice deciphering definitions before proving.
-/

def non_decreasing (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

def is_seq_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

-- 0038
example (M : ℝ) (h : is_seq_sup M u) (h' : non_decreasing u) :
seq_limit u M :=
begin
  intros e e0,
  have k: ∃ n₀, u n₀ ≥ M - e,
    from h.2 e (by linarith),
  cases k with n₀ p,
  use n₀,
  intros n hn,
  rw abs_le,
  split,
  {
    have k1: u n₀ ≤ u n,
      from h' n₀ n hn,
    calc -e ≤ u n₀ - M: by linarith
    ... ≤ u n -M: by linarith,
  },
  {
    have: u n ≤ M + e,
    {calc u n ≤ M: h.1 n
    ... ≤ M + e: by linarith},
    linarith,
  },
end


