import data.real.basic


/- 重写命题 -/
/- 示例
  mul_assoc a b c : a * b * c = a * (b * c)
  mul_comm a b : a * b = b * a   -/

example (x y z: ℝ): x * y * z = z * y * x :=
begin
  rw mul_comm (x * y ) z,
  rw mul_comm x y,
  rw mul_assoc,
end

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

/- 反证法 -/




















