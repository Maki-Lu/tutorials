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

