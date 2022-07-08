import data.real.basic

/- 严格证明法 -/
example (P Q: Prop) (pq: P → Q): ¬ Q → ¬ P :=
begin
  intros nq p,
  exact nq (pq p),
end

example (P Q: Prop) (npnq: ¬ P → ¬ Q): Q → P :=
begin
  intro q,
  by_contra np,
  exact npnq np q,
end

/- 直接取逆否命题 -/
example (P Q: Prop) (pq: P → Q): ¬ Q → ¬ P :=
begin
  contrapose,
  push_neg,
  exact pq,  
end

example (P Q: Prop) (pq: P → Q): ¬ Q → ¬ P :=
begin
  contrapose!,
  exact pq,
end

example (P Q: Prop) (npnq: ¬ P → ¬ Q): Q → P :=
begin
  contrapose,
  exact npnq,
end



/- 用三种方法证明逆否命题的等价性 -/

/- 方法一 -/
example (P Q: Prop) (pq: P → Q): ¬ Q → ¬ P :=
begin
  sorry,
end

/- 方法二 -/
example (P Q: Prop) (pq: P → Q): ¬ Q → ¬ P :=
begin
  sorry,
end

/- 方法三 -/
example (P Q: Prop) (pq: P → Q): ¬ Q → ¬ P :=
begin
  sorry,
end




