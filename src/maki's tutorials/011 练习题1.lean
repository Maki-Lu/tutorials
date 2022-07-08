import data.real.basic


example (P Q R: Prop): P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R):=
begin
  split,
  {
    intro pqr,
    cases pqr with p qr,
    {
      split,
      left, exact p,
      left, exact p,
    },
    {
      cases qr with q r,
      split,
      right, exact q,
      right, exact r,
    },
  },
  {
    intro pqpr,
    cases pqpr with pq pr,
    by_cases hp: P,
    {
      left, exact hp,
    },
    {
      right,
      split,
      cases pq with p q,
      {
        exfalso,
        exact hp p,
      },
      exact q,
      cases pr with p r,
      {
        exfalso,
        exact hp p,
      },
      exact r,
    },
  },
end

example (P Q R: Prop): P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R):=
begin
  split,
  {
    intro pqr,
    cases pqr with p qr,
    cases qr with q r,
    left,
    exact ⟨p, q⟩,
    right,
    exact ⟨p, r⟩,
  }, 
  {
    intro pqpr,
    cases pqpr with pq pr,
    { 
      cases pq with p q,
      split,
      exact p,
      left,
      exact q
    },
    { 
      cases pr with p r,
      split,
      exact p,
      right,
      exact r,
    },
  },
end



