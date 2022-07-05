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







