import data.real.basic


/- 反向证明 -/
example (P Q R: Prop) (p: P) (pq: P → Q) (qr: Q → R): R :=
begin
  suffices q: Q,
    exact qr q,
  suffices p: P,
    exact pq p,
  exact p,
end

example (P Q R: Prop) (p: P) (pq: P → Q) (qr: Q → R): R :=
begin
  suffices q: Q,
    exact qr q,
  suffices p: P,
    exact pq p,
  exact p,
end

example (P Q R: Prop) (p: P) (p_qr: P → (Q → R)) (q: Q): R :=
begin
  suffices qr: Q → R,
    exact qr q,
  suffices p: P,
    exact p_qr p,
  exact p,
end

