import data.real.basic

open_locale classical

/-
Theoretical negations.

This file is for people interested in logic who want to fully understand
negations.

Here we don't use `contrapose` or `push_neg`. The goal is to prove lemmas
that are used by those tactics. Of course we can use
`exfalso`, `by_contradiction` and `by_cases`.

If this doesn't sound like fun then skip ahead to the next file.
-/

section negation_prop

variables P Q : Prop

-- 0055
example : (P → Q) ↔ (¬ Q → ¬ P) :=
begin
  split,
  { intros pq nq p,
    exact nq (pq p)},
  { intros nqnp p,
    by_contra nq,
    exact nqnp nq p,
  },
end

-- 0056
lemma non_imp (P Q : Prop) : ¬ (P → Q) ↔ P ∧ ¬ Q :=
begin
  split,
  { intro h,
    by_cases p: P,
    { have nq: ¬ Q,
      {intro q, apply h, intro p, exact q},
      exact ⟨ p, nq⟩},
    { exfalso,
      apply h,
      intro p',
      exfalso,
      exact p p'},
  },
  { rintro ⟨p, nq⟩ pq,
    exact nq (pq p),
  },
end

-- In the next one, let's use the axiom
-- propext {P Q : Prop} : (P ↔ Q) → P = Q

-- 0057
example (P : Prop) : ¬ P ↔ P = false :=
begin
  split,
  { 
    intro np,
    apply propext,
    split,
    { apply np },
    { intro h, exfalso, exact h },
  },
  { intro np,
    rw np,
    exact id,
  },
end

end negation_prop

section negation_quantifiers
variables (X : Type) (P : X → Prop)

-- 0058
example : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x :=
begin
  split,
  { intro hyp,
    by_contra k,
    apply hyp,
    intros x,
    by_contra npx,
    apply k,
    use x,
  },
  { rintros ⟨x,npx⟩ apx,
    exact npx (apx x),
  },
end

-- 0059
example : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x :=
begin
  split,
  { intros hyp x px,
    apply hyp,
    use x,
    exact px,
  },
  { rintros hyp ⟨x, px⟩,
    exact hyp x px,
  },
end

-- 0060
example (P : ℝ → Prop) : ¬ (∃ ε > 0, P ε) ↔ ∀ ε > 0, ¬ P ε :=
begin
  split,
  { intros hyp e e0 pe,
    apply hyp,
    use e, exact ⟨e0, pe⟩,
  },
  { rintros hyp ⟨e, e0, pe⟩,
    exact hyp e e0 pe,
  },
end

-- 0061
example (P : ℝ → Prop) : ¬ (∀ x > 0, P x) ↔ ∃ x > 0, ¬ P x :=
begin
  split,
  { intro hyp,
    by_contra k,
    apply hyp,
    intros x x0,
    by_contra npx,
    apply k,
    use x,
    exact ⟨x0, npx⟩,
  },
  { rintros ⟨x, x0, npx⟩ apx,
    exact npx (apx x x0),
  },
end

end negation_quantifiers

