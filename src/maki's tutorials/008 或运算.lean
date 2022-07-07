import data.real.basic

/- 结论用了或运算：直接证明其中的一个 -/
example (P Q: Prop) (p: P): P ∨ Q:=
begin
  left,
  exact p,
end

example (P Q: Prop) (q: Q): P ∨ Q:=
begin
  right,
  exact q,
end

/- 条件用了或运算：分类讨论 -/
example (P Q: Prop) (pq: P ∨ Q): Q ∨ P:=
begin
  cases pq with p q,
  { right,
    exact p},
  { left,
    exact q},
end

example (P Q R: Prop) (p_qr: P ∨ Q ∨ R): (P ∨ Q) ∨ R:=
begin
  cases p_qr with p qr,
  { have pq: P ∨ Q,
      left, exact p,
    left, exact pq,
  },
  { cases qr with q r,
    { have pq: P ∨ Q,
        right, exact q,
      left, exact pq},
    { right, exact r},
  },
end




/- 练习题 -/









