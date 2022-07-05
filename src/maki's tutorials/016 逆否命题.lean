import data.real.basic

example (P Q: Prop) (pq: P → Q): (¬ Q → ¬ P) :=
begin
  intro p,
  exact ⟨pq p, pr p⟩,
end








