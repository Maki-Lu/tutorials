import data.real.basic

/- 结论用了存在量词 -/
example: ∃ x : ℝ, 2 * x = 4 :=
begin
  use 2,
  by ring,
end

example: ∃ x : ℝ, ∀ y : ℝ, x * y = y :=
begin
  use 1,
  intro y,
  by ring,
end

example: ∃ x : ℝ, ∀ y : ℝ, x + y = y :=
begin
  use 0,
  intro y,
  by ring,
end

example (P: ℝ → Prop) (Px: ∀ x, P x): ∃ x, P x:=
begin
  use 1,
  specialize Px 1,
  exact Px,
end

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


/- 条件用了存在量词 -/

example (P: ℝ → (ℝ → Prop)) (Hyp: ∃ x, ∀ y, P x y): ∀ y, ∃ x, P x y :=
begin
  intro y,
  cases Hyp with x Pxy,
  use x,
  specialize Pxy y,
  exact Pxy,
end

example (P: ℝ → (ℝ → Prop)) (Hyp: ∃ x, ∀ y, P x y): ∀ y, ∃ x, P x y :=
begin
  intro y,
  cases Hyp with x0 Px0y,
  use x0,
  specialize Px0y y,
  exact Px0y,
end



/- 练习题 -/







