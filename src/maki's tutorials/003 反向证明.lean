import data.real.basic


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
example (P: ℝ → Prop): ∀x, (P x → P x) :=
begin
  intro x,
  exact id,
end

example: ∀ x y: ℝ, x + y = y + x :=
begin
  intros x y,
  by ring,
end

