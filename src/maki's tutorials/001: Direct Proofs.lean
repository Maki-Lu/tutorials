import data.real.basic

/- 条件证明  -/

example (P: Prop) : P → P :=
begin
  intro p,
  exact p,
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

/- 中间结论 -/
example (P Q: Prop) (p: P) (pq: P → Q): Q :=
begin
  have:= pq p,
  exact this,
end

example (P Q: Prop) (p: P) (pq: P → Q): Q :=
begin
  have q := pq p,
  exact q,
end

example (P Q: Prop) (p: P) (pq: P → Q): Q :=
begin
  have q: Q,
    exact pq p,
  exact q,
end

example (P Q R: Prop) (p: P) (pq: P → Q) (qr: Q → R): R :=
begin
  have q := pq p,
  have r := qr q,
  exact r,
end

example (P Q R: Prop) (p: P) (pq: P → Q) (qr: Q → R): R :=
begin
  have q := pq p,
  exact qr q,
end

example (P Q R: Prop) (p: P) (p_qr: P → (Q → R)) (q: Q): R :=
begin
  have qr := p_qr p,
  exact qr q,
end


/- 只须证明 -/

example (P Q R: Prop) (p: P) (pq: P → Q) (qr: Q → R): R :=
begin
  suffices q: Q,
    exact qr q,
  exact pq p,
end

example (P Q R: Prop) (p: P) (pq: P → Q) (qr: Q → R): R :=
begin
  suffices q: Q,
    exact qr q,
  have q := pq p,
  exact q,
end

/- 全称量词 -/
example (P: ℝ → Prop) ∀ x : ℝ , P x:=
begin
  suffices q: Q,
    exact qr q,
  have q := pq p,
  exact q,
end



























