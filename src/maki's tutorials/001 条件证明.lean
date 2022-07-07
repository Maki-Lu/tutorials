import data.real.basic

/- 条件证明  -/
example (P: Prop) : P → P :=
begin
  intro p,
  exact p,
end

example (P: Prop) : P → P :=
begin
  exact id,
end

example (P Q: Prop) : P → (Q → P) :=
begin
  intro p,
  intro q,
  exact p,
end

example (P Q R: Prop) : P → (Q → (R → Q)) :=
begin
  intro p,
  intro q,
  intro r,
  exact q,
end

example (P Q: Prop) : (P → Q) → (P → Q) :=
begin
  intro pq,
  exact pq,
end


/- 三段论 -/
example (P Q: Prop) (p: P) (pq: P → Q): Q :=
begin
  exact pq p,
end

example (P Q R: Prop) (p: P) (pq: P → Q) (qr: Q → R): R :=
begin
  exact qr (pq p),
end

example (P Q R: Prop) (p: P) (p_qr: P → (Q → R)) (q: Q): R :=
begin
  exact p_qr p q,
end

example (P Q R: Prop)  (pq: P → Q) (qr: Q → R): P → R :=
begin
  intro p,
  exact qr (pq p),
end



/- 练习题 -/

example (P Q R: Prop)  (pqr: P → (Q → R)): Q → (P → R) :=
begin
  sorry
end

example (P Q R: Prop)  (qr: Q → R): (P → Q) → (P → R) :=
begin
  sorry
end

example (P Q R S: Prop): (P → Q) → (Q → R) → (R → S) → (P → S) :=
begin
  sorry
end


