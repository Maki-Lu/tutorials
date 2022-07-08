import data.real.basic

/- 递等式证明 -/
example (x y z: ℝ): x * y * z = z * y * x :=
begin
  calc x * y * z = z * (x * y): by rw mul_comm
    ... = z * (y * x): by rw mul_comm x y
    ... = z * y * x: by rw mul_assoc,
end

example (x y z: ℝ): x * y * z = z * y * x :=
begin
  by ring,
end



/- 练习题 -/
/- 用递等式证明 -/

example (x y z w: ℝ): x * ((y * z) * w) = (x * y) * (z * w) :=
begin
  sorry,
end

example (x y z w: ℝ): x * y * z * w = w * z * y * x :=
begin
  sorry,
end





