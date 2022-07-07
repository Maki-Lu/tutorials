import data.real.basic

/- 排中律 -/

example (P: Prop): P ∨ ¬ P:=
begin
  by_cases p: P,
  {
    left,
    exact p,
  },
  {
    right,
    exact p,
  },
end

example (P Q: Prop) (pq: P → Q): ¬ P ∨ Q :=
begin
  by_cases p: P,
  { have q := pq p,
    right,
    exact q,
  },
  { left,
    exact p,
  },
end



/- 练习题 -/











