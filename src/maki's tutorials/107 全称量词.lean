import data.real.basic

/- 全称量词 -/
example (P: ℝ → Prop): ∀x, (P x → P x) :=
begin
  intro x,
  exact id,
end

example: ∀ x y: ℝ, x + y = y + x :=
begin
  intros x y,
  by ring,
end