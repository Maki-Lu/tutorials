import data.real.basic

def yx_xxy (A: set ℝ) := ∀ x y : ℝ, (x ∈ A ∧ y ∈ A)→ x*y=y*x 

/- 命题重写 -/
/- 示例
  （乘法结合律） mul_assoc a b c : a * b * c = a * (b * c)
  （乘法交换律） mul_comm a b : a * b = b * a   -/



/-instance : semigroup A          := by apply_instance-/

universes u v
variables {G : Type u} {H : Type v}

class special (G: Type u) [group G] : Prop := (haha: ∀ x y: G, x*y=y*x)

def ab [group G] := ∀ x y: G, x*y=y*x

example [group G] [sg: special G] (x y: G): x*y=y*x :=
begin
  
end

