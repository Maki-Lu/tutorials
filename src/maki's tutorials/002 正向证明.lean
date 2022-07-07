import data.real.basic

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



/- 练习题 -/







