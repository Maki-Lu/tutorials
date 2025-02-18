import tuto_lib
/-
This file continues the elementary study of limits of sequences. 
It can be skipped if the previous file was too easy, it won't introduce
any new tactic or trick.

Remember useful lemmas:

abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y

abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|

abs_sub_comm (x y : ℝ) : |x - y| = |y - x|

ge_max_iff (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q

le_max_left p q : p ≤ max p q

le_max_right p q : q ≤ max p q

and the definition:

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

You can also use a property proved in the previous file:

unique_limit : seq_limit u l → seq_limit u l' → l = l                   '

def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m
-/


variable { φ : ℕ → ℕ}

/-
The next lemma is proved by an easy induction, but we haven't seen induction
in this tutorial. If you did the natural number game then you can delete 
the proof below and try to reconstruct it.
-/
/-- An extraction is greater than id -/
lemma id_le_extraction' : extraction φ → ∀ n, n ≤ φ n :=
begin
  intros hyp n,
  induction n with n hn,
  { exact nat.zero_le _ },
  { exact nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)]) },
end

/-- Extractions take arbitrarily large values for arbitrarily large 
inputs. -/
-- 0039
lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N :=
begin
  intros hyp N N',
  use max N N',
  split,
  exact le_max_right N N',
  calc  φ (max N N') ≥ max N N': id_le_extraction' hyp (max N N')
  ... ≥ N: le_max_left N N',
end

/-- A real number `a` is a cluster point of a sequence `u` 
if `u` has a subsequence converging to `a`. 

def cluster_point (u : ℕ → ℝ) (a : ℝ) :=
∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a
-/

variables {u : ℕ → ℝ} {a l : ℝ}

/-
In the exercise, we use `∃ n ≥ N, ...` which is the abbreviation of
`∃ n, n ≥ N ∧ ...`.
Lean can read this abbreviation, but displays it as the confusing:
`∃ (n : ℕ) (H : n ≥ N)`
One gets used to it. Alternatively, one can get rid of it using the lemma
  exists_prop {p q : Prop} : (∃ (h : p), q) ↔ p ∧ q
-/

/-- If `a` is a cluster point of `u` then there are values of
`u` arbitrarily close to `a` for arbitrarily large input. -/
-- 0040
lemma near_cluster :
  cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
begin
  intros hyp e e0 N,
  rcases hyp with ⟨φ, φ_extr, hφ⟩,
  cases hφ e e0 with N' hN',
  rcases extraction_ge φ_extr N N' with ⟨q, hq, hq'⟩,
  exact ⟨φ q, hq', hN' _ hq⟩, 
end

/-
The above exercice can be done in five lines. 
Hint: you can use the anonymous constructor syntax when proving
existential statements.
-/

/-- If `u` tends to `l` then its subsequences tend to `l`. -/
-- 0041
lemma subseq_tendsto_of_tendsto' (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l :=
begin
  intros e e0,
  cases h e e0 with N hN,
  use N,
  intros n hn,
  have k: φ n ≥ N,
  {calc φ n ≥ n: id_le_extraction' hφ n
  ... ≥ N: by linarith},
  exact hN (φ n) k,
end

/-- If `u` tends to `l` all its cluster points are equal to `l`. -/
-- 0042
lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l :=
begin
  rcases ha with ⟨φ, φ_extr, lim_a⟩,
  have k: seq_limit (u ∘ φ) l, from subseq_tendsto_of_tendsto' hl φ_extr,
  exact unique_limit lim_a k,
end

/-- Cauchy_sequence sequence -/
def cauchy_sequence (u : ℕ → ℝ) := ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

-- 0043
example : (∃ l, seq_limit u l) → cauchy_sequence u :=
begin
  intros conv e e0,
  cases conv with l lim,
  cases lim (e/2) (by linarith) with N hN,
  use N,
  intros p q hp hq,
  calc |u p - u q|= |(u p - l) + (l - u q)|: by congr' 1; ring
  ... ≤ |(u p - l)| + |l - u q|: by apply abs_add
  ... = |(u p - l)| + |u q - l|: by rw abs_sub_comm (u q) l
  ... ≤ e: by linarith [(hN p hp), (hN q hq)],
end


/- 
In the next exercise, you can reuse
 near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε
-/
-- 0044
example (hu : cauchy_sequence u) (hl : cluster_point u l) : seq_limit u l :=
begin
  intros e e0,
  rcases hl with ⟨φ, φ_extr, sub_lim⟩,
  cases sub_lim (e/2) (by linarith) with N1 hN1,
  cases hu (e/2) (by linarith) with N2 hN2,
  use max N1 N2,
  intros n hn,
  have k := 
    calc N2 ≤ max N1 N2: le_max_right N1 N2
    ... ≤ n: by linarith
    ... ≤ φ n: id_le_extraction' φ_extr n,
  have k1: |u n - u (φ n) | ≤ e/2,
  {exact hN2 n (φ n) (by linarith[le_max_right N1 N2]) k},
  have k2: |u (φ n) - l | ≤ e/2,
  {exact hN1 n (by linarith[le_max_left N1 N2])},
  calc |u n - l| = |u n - u (φ n) + (u (φ n)-l ) |: by congr' 1; ring
  ... ≤ |u n - u (φ n) | + | (u (φ n)-l ) |: by apply abs_add
  ... ≤ e: by linarith,
end

