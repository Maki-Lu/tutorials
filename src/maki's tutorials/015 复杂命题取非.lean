import data.real.basic

/- 用严格证明的方法取非 -/
example (P: ℝ → Prop) (npx: ∀ x, ¬ P x): ¬ ∃ x, P x :=
begin
  intro epx,
  cases epx with x px,
  specialize npx x,
  exact npx px,
end

example (P: ℝ → Prop) (npx: ∀ x, ¬ P x): ¬ ∃ x, P x :=
begin
  rintros ⟨x, px⟩,
  specialize npx x,
  exact npx px,
end

example (P: ℝ → Prop) (npx: ∃ x, ¬ P x): ¬ ∀ x, P x :=
begin
  intro apx,
  cases npx with x npx,
  specialize apx x,
  exact npx apx,
end

example (P: ℝ → Prop) (npx: ¬ ∃ x, P x): ∀ x, ¬ P x :=
begin
  intros x px,
  have epx: ∃ x, P x,
    use x,
    exact px,
  exact npx epx,
end

example (P: ℝ → Prop) (npx: ¬ ∀ x, P x): ∃ x, ¬ P x :=
begin
  by_contra nenpx,
  apply npx, /- 证明伪命题的一种常用方法 -/
  intro x,
  by_contra npx,
  have enpx: ∃ x, ¬ P x,
    use x,
  exact nenpx enpx,
end

/- 直接取非 -/
example (P: ℝ → Prop) (npx: ∀ x, ¬ P x): ¬ ∃ x, P x :=
begin
  push_neg,
  exact npx,
end

example (P: ℝ → Prop) (npx: ∃ x, ¬ P x): ¬ ∀ x, P x :=
begin
  push_neg,
  exact npx,
end

example (P: ℝ → Prop) (npx: ¬ ∃ x, P x): ∀ x, ¬ P x :=
begin
  push_neg at npx,
  exact npx,
end

example (P: ℝ → Prop) (npx: ¬ ∀ x, P x): ∃ x, ¬ P x :=
begin
  push_neg at npx,
  exact npx,
end

