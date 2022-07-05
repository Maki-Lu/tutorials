import data.real.basic


/- 反向证明 -/
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


