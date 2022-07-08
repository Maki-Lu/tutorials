import data.real.basic

/- 结论是等价命题：分别证明两个方向 -/
example (P Q: Prop) (pq: P → Q) (qp: Q → P): P ↔ Q:=
begin
  split,
  exact pq,
  exact qp,
end

/- 结论是等价命题：直接证明两个方向 -/
example (P Q: Prop) (pq: P → Q) (qp: Q → P): P ↔ Q:=
begin
  exact ⟨pq, qp⟩,
end

/- 结论是等价命题：用逻辑的递等式证明 -/
example (P: Prop): ¬ ¬ ¬ ¬ P ↔ P:=
begin
  calc ¬ ¬ ¬ ¬ P ↔ ¬ ¬ P: by rw not_not
  ... ↔ P: by rw not_not,
end


/- 条件是等价命题 -/
example (P Q: Prop) (Hyp: P ↔ Q): Q ↔ P:=
begin
  cases Hyp with pq qp,
  split,
  exact qp,
  exact pq,
end

example (P Q: Prop) (Hyp: P ↔ Q): Q ↔ P:=
begin
  rw Hyp,
end

example (P Q R: Prop) (Hyp: P ↔ Q) (Hyp': Q ↔ R): P ↔ R:=
begin
  cases Hyp with pq qp,
  cases Hyp' with qr rq,
  split,
  {
    intro p,
    exact qr (pq p),
  },
  {
    intro r,
    exact qp (rq r),
  },
end

example (P Q R: Prop) (Hyp: P ↔ Q) (Hyp': R ↔ P): Q ↔ R:=
begin
  rw ← Hyp, /- 表示代入反向的箭头 -/
  rw Hyp',
end



/- 练习题 -/

example (P Q R S: Prop) (Hyp1: P ↔ Q) (Hyp2: R ↔ S) (Hyp3: S ↔ P): R ↔ Q:=
begin
  sorry,
end

example (P Q R: Prop): ((P → Q) ∧ (P → R)) ↔  (P → (Q ∧ R)) :=
begin
  sorry,
end

example (P Q R: Prop): (P → (Q → R)) ↔  ((P ∧ Q ) → R) :=
begin
  sorry,
end

