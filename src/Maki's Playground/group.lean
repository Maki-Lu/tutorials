import data.real.basic

def yx_xxy (A: set ℝ) := ∀ x y : A, y * x = x * x * y

/- 命题重写 -/
/- 示例
  （乘法结合律） mul_assoc a b c : a * b * c = a * (b * c)
  （乘法交换律） mul_comm a b : a * b = b * a   -/



/-instance : semigroup A          := by apply_instance-/

example (A: set ℝ) (hyp: yx_xxy A) (x y: ℝ): (x ∈ A ∧ y ∈ A) →  y * x = x * x * y := /-x * x * y * y * x * x * y * y = x * y :=-/
begin
  rintro ⟨hx, hy⟩,
  
  
end

