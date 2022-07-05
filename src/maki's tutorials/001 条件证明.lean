import data.real.basic

/- 条件证明  -/

example (P: Prop) : P → P :=
begin
  intro p,
  exact p,
end

example (P: Prop) : P → P :=
begin
  exact id,
end

example (P Q: Prop) : P → (Q → P) :=
begin
  intro p,
  intro q,
  exact p,
end

example (P Q R: Prop) : P → (Q → (R → Q)) :=
begin
  intro p,
  intro q,
  intro r,
  exact q,
end

example (P Q: Prop) : (P → Q) → (P → Q) :=
begin
  intro pq,
  exact pq,
end


/- 三段论 -/
example (P Q: Prop) (p: P) (pq: P → Q): Q :=
begin
  exact pq p,
end

example (P Q R: Prop) (p: P) (pq: P → Q) (qr: Q → R): R :=
begin
  exact qr (pq p),
end

example (P Q R: Prop) (p: P) (p_qr: P → (Q → R)) (q: Q): R :=
begin
  exact p_qr p q,
end






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





















