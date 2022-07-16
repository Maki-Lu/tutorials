import data.real.basic

/- 命题重写 -/
/- 示例
  （乘法结合律） mul_assoc a b c : a * b * c = a * (b * c)  -/

universes u v
variables {G : Type u} {H : Type v}

class ab (G: Type u) [group G] : Prop := (ab: ∀ x y: G, x*y=y*x)

example [group G] [h: ab G] (x y: G): x*y=y*x :=
begin
  rw h.ab,
end


def hab [group G] (x y: G) := x*y=y*x

example [group G] (x y: G) (h: hab x y): x*y=y*x :=
begin
  have h: x*y=y*x,
    exact h,
  rw h,
end

def h1 [group G] (x y: G) := y*x=x*x*y


local attribute [simp] mul_assoc

example [gg: group G] (x y: G) [h: h1 x y]: x*y*x*y=x^3*y^2 :=
begin
  have h1: y*x=x*x*y,
    exact h,
  repeat{rw mul_assoc, rw mul_assoc, try{rw h1}},
  
  sorry,
  

end



example (x y z w: ℝ): x * y * z * w = x * ((y * z) * w) :=
begin
  rw mul_assoc,
  rw ← mul_assoc,
  

  repeat{rw mul_assoc,},
end



