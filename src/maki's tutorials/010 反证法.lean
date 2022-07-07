import data.real.basic


/- 直接证伪 -/
example (P: Prop) (p: P) (np: ¬P): false :=
begin
  exact np p,
end

example (P Q: Prop) (p: P) (pq: P → Q) (nq: ¬Q): false :=
begin
  exact nq (pq p),
end

/- 突然宣布要证伪，用虚真命题 -/
example (P Q: Prop) (p: P) (np: ¬P): Q :=
begin
  exfalso,
  exact np p,
end

example (P Q: Prop) (Hyp: ¬ P ∨ Q): P → Q :=
begin
  cases Hyp with np q,
  { 
    intro p,
    exfalso,
    exact np p,
  },
  {
    intro p,
    exact q,
  },
end

/- 反证法：否定形式的反证法 -/
example (P Q: Prop) (p: P) (nq: ¬ Q): ¬ (P → Q) :=
begin
  intro pq,
  exact nq (pq p),
end

example (P Q: Prop) (Hyp: ¬ P ∨ ¬ Q): ¬ (P ∧ Q) :=
begin
  intro pq,
  cases pq with p q,
  cases Hyp with np nq,
  exact np p,
  exact nq q,
end

example (P Q: Prop) (Hyp: ¬ P ∧ ¬ Q): ¬ (P ∨ Q) :=
begin
  intro pq,
  cases Hyp with np nq,
  cases pq with p q,
  exact np p,
  exact nq q,
end


/- 反证法：肯定形式的反证法 -/
example (P Q: Prop) (nqnp: ¬ Q → ¬ P): P → Q :=
begin
  intro p,
  by_contra nq,
  exact (nqnp nq) p,
end

example (P Q: Prop) (pq: P → Q): ¬ Q → ¬ P :=
begin
  intro nq,
  by_contra p,
  exact nq (pq p),
end



/- 练习题 -/











