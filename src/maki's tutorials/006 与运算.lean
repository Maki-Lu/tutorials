import data.real.basic

/- 结论用了与运算：直接证明 -/
example (P Q: Prop) (p: P) (q: Q): P ∧ Q:=
begin
  exact ⟨p, q⟩,
end

example (P Q R: Prop) (p: P) (q: Q) (r: R): P ∧ Q ∧ R:=
begin
  exact ⟨p, q, r⟩,
end

example (P Q R: Prop) (p: P) (pq: P → Q) (qr: Q → R): Q ∧ R:=
begin
  have q: Q,
    exact pq p,
  have r: R,
    exact qr q,
  exact ⟨q, r⟩,
end

/- 结论用了与运算：分开证明 -/
example (P Q: Prop) (p: P) (q: Q): P ∧ Q:=
begin
  split,
  exact p,
  exact q,
end

example (P Q R: Prop) (p: P) (q: Q) (r: R): P ∧ Q ∧ R:=
begin
  split,
  exact p,
  split,
  exact q,
  exact r,
end

example (P Q R: Prop) (p: P) (pq: P → Q) (qr: Q → R): Q ∧ R:=
begin
  split,
  exact pq p,
  exact qr (pq p),
end

/- 条件用了与运算 -/
example (P Q: Prop) (pq: P ∧ Q): P :=
begin
  cases pq with p q,
  exact p,
end

example (P Q R: Prop) (pqr: P ∧ Q ∧ R): Q :=
begin
  cases pqr with p qr,
  cases qr with q r,
  exact q,
end



/- 练习题 -/







