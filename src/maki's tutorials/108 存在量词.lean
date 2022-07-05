import data.real.basic

/- 存在量词 -/
example: ∃ x : ℝ, 2*x = 4 :=
begin
  use 2,
  by ring,
end

/- 综合练习 -/
example: ∀ x : ℝ, ∃ y : ℝ, x = 2 * y :=
begin
  intro x,
  use x/2,
  by ring,
end

example: ∀ x : ℝ, ∃ y : ℝ, y > x :=
begin
  intro x,
  use x + 1,
  by linarith,
end

example: ∃ x : ℝ, ∀ y : ℝ, ( y ≤ 1 → y < x ) :=
begin
  use 2,
  intro y,
  intro y1,
  by linarith,
end

example: ∃ x : ℝ, ∀ y : ℝ, ( y ≤ 1 → y < x ) :=
begin
  use 2,
  intros y y1,
  by linarith,
end
