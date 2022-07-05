import data.real.basic


/- 命题重写 -/
/- 示例
  （乘法结合律） mul_assoc a b c : a * b * c = a * (b * c)
  （乘法交换律） mul_comm a b : a * b = b * a   -/

example (x y z: ℝ): x * y * z = z * y * x :=
begin
  rw mul_comm (x * y) z,
  rw mul_comm x y,
  rw mul_assoc,
end

example (x y z w: ℝ): x * y * z * w = x * (y * (z * w)) :=
begin
  rw mul_assoc,
  rw mul_assoc,
end

/- 示例
  （双重否定律） not_not p : ¬ ¬ p ↔ p  -/

example (p: Prop): ¬ ¬ p ↔ p :=
begin
  rw not_not,
end

example (p: Prop):  ¬ ¬ ¬ ¬ ¬ ¬ p ↔ p :=
begin
  rw not_not,
  rw not_not,
  rw not_not,
end

example (p: Prop): p ↔ ¬ ¬ p :=
begin
  rw not_not,
end

example (p: Prop):  p ↔ ¬ ¬ ¬ ¬ ¬ ¬ p :=
begin
  rw not_not,
  rw not_not,
  rw not_not,
end



