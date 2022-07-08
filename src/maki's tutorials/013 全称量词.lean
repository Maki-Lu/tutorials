import data.real.basic

/- 结论用了全称量词 -/
example (P: ℝ → Prop): ∀ x, (P x → P x) :=
begin
  intro x,
  exact id,
end

example: ∀ x y : ℝ, x * y = y * x :=
begin
  intros x y,
  rw mul_comm,
end

/- 条件用了全称量词 -/
example (P: ℝ → Prop) (Px: ∀ x, P x): P 5 :=
begin
  specialize Px 5,
  exact Px,
end


example (P: ℝ → ( ℝ → Prop)) (Pxy: ∀ x, ∀ y, P x y): P 2 3 :=
begin
  specialize Pxy 2 3,
  exact Pxy,
end

example (P: ℝ → ( ℝ → Prop)) (P2y: ∀ y, P 2 y): P 2 3 :=
begin
  specialize P2y 3,
  exact P2y,
end

example (P: ℝ → ( ℝ → Prop)) (Pxy: ∀ x, ∀ y, P x y): ∀ y, ∀ x, P x y :=
begin
  intros y x,
  specialize Pxy x y,
  exact Pxy,
end



/- 练习题 -/

example (P: ℝ → ( ℝ → (ℝ → Prop))) (Pxy: ∀ x, ∀ y, ∀ z, P x y z): ∀ z, ∀ y, ∀ x, P x y z:=
begin
  sorry,
end

example (P: ℝ → Prop) (Hyp: ∀ x, (x > 0) → P x) : P 1 :=
begin
  sorry,
end

example (P: Prop) (Q: ℝ → Prop) (Hyp: ∀ x, P → Q x) : P → (∀ x, Q x) :=
begin
  sorry,
end


