import field_theory.ratfunc
import data.complex.basic

-- ring of integers ℤ
example : comm_ring ℤ := by apply_instance

-- field of fractions ℚ
noncomputable example : ℚ ≃ₐ[ℤ] fraction_ring ℤ := (fraction_ring.alg_equiv ℤ ℚ).symm

-- ring of polynomials over the complexes
noncomputable example : comm_ring (polynomial ℂ) := by apply_instance

-- field of fractions ℂ(X)
noncomputable example : ratfunc ℂ ≃ₐ[ℂ] fraction_ring (polynomial ℂ) :=
(fraction_ring.alg_equiv (polynomial ℂ) (ratfunc ℂ)).symm.restrict_scalars ℂ

-- An element of f(X) : ℂ(X) is a “rational function,” i.e., a quotient
-- of two polynomials, P(X), Q(X) : ℂ[X], Q(X) ≠ 0;
-- we can always require that Q(X) is monic, i.e., its leading coefficient is 1.
example (f : ratfunc ℂ) : ∃ (p q : polynomial ℂ) (hq : q ≠ 0) (hm : q.monic),
  f = ratfunc.mk p q :=
⟨f.num, f.denom, f.denom_ne_zero, f.monic_denom,
  by simp only [ratfunc.mk_eq_div, ratfunc.num_div_denom]⟩
