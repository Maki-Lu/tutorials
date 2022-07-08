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



/- 练习题（用反向证明） -/

example (P Q R: Prop)  (pqr: P → (Q → R)): Q → (P → R) :=
begin
  sorry,
end

example (P Q R: Prop)  (qr: Q → R): (P → Q) → (P → R) :=
begin
  sorry,
end

example (P Q R S: Prop): (P → Q) → (Q → R) → (R → S) → (P → S) :=
begin
  sorry,
end





