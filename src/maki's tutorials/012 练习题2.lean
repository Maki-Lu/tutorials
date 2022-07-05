import data.real.basic

example (P Q R: Prop) (pq: P → Q) (pr: P → R): P → (Q ∧ R) :=
begin
  intro p,
  exact ⟨pq p, pr p⟩,
end

example (P Q R: Prop) (pr: P → R) (qr: Q → R): (P ∨ Q) → R :=
begin
  intro pq,
  cases pq with p q,
  exact pr p,
  exact qr q,
end

example (P Q R: Prop) (pqpr: (P → Q) ∨ (P → R)): P → (Q ∨ R) :=
begin
  intro p,
  cases pqpr with pq pr,
  left, exact pq p,
  right, exact pr p,
end

example (P Q R: Prop) (prqr: (P → R) ∨ (Q → R)): (P ∧ Q) → R :=
begin
  intro pq,
  cases pq with p q,
  cases prqr with pr qr,
  exact pr p,
  exact qr q,
end
