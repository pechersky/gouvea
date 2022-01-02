import analysis.complex.polynomial
import data.polynomial.taylor
import data.nat.digits
import data.fin.vec_notation

open polynomial
open_locale big_operators

-- ℤ is a ring where there is unique factorization
example : unique_factorization_monoid ℤ := by apply_instance

-- any integer can be expressed uniquely by ±1 times a product of primes
-- N.B. this is not true for 0, since the empty product is 1,
-- and 0 is not a prime. the only product that can equal 0 must have 0 in it
example (x : ℤ) (hx : x ≠ 0) : ∃ (f : multiset ℤ) (hf : ∀ p ∈ f, prime p),
  f.prod = x ∨ f.prod = -x :=
begin
  obtain ⟨f, hf, u, rfl⟩ := unique_factorization_monoid.exists_prime_factors x hx,
  refine ⟨f, hf, _⟩,
  rcases int.units_eq_one_or u with rfl|rfl;
  simp [units.coe_neg]
end

-- ℂ[X] is a ring where there is unique factorization
example : unique_factorization_monoid (polynomial ℂ) := by apply_instance

-- any polynomial (over the complexes) can be uniquely expressed as
-- P(X) = α(X − α₁)(X − α₂)...(X − αₙ)
-- where α, α₁, α₂, ..., αₙ are complex numbers
example (p : polynomial ℂ) : ∃ (α : ℂ) (f : multiset ℂ),
  p = α • (f.map (λ a, (X : polynomial ℂ) - C a)).prod :=
begin
  refine ⟨p.leading_coeff, p.roots, _⟩,
  rw [smul_eq_C_mul, C_leading_coeff_mul_prod_multiset_X_sub_C],
  rw ←splits_iff_card_roots,
  exact is_alg_closed.splits p
end

-- √2 is a root of Y ^ 2 − 2, so is an algebraic number
example : is_algebraic ℤ (real.sqrt 2) :=
begin
  refine ⟨X ^ 2 - 2, _, by simp⟩,
  intro H,
  simpa using congr_arg (eval 0) H
end

-- f(X) = √(X ^ 3 − 3 X + 1),
-- which is a root of Y ^ 2 − (X ^ 3 − 3 X + 1), is an algebraic function
example : is_algebraic (polynomial ℤ) (λ x, complex.cpow (x ^ 3 - 3 • x + 1) (1 / 2)) :=
begin
  refine ⟨X ^ 2 - C (X ^ 3 - 3 • X + 1), _, _⟩,
  { intro H,
    replace H := congr_arg (eval 0) (congr_arg (eval 0) H),
    simpa using H },
  { ext1 x,
    suffices : ((x ^ 3 - 3 * x + 1) ^ (2 : ℂ)⁻¹) ^ 2 - (x ^ 3 - 3 * x + 1) = 0,
    { simpa },
    have h2 : (2 : ℂ) = (2 : ℝ),
    { simp },
    rw [←complex.cpow_nat_cast, ←complex.cpow_mul],
    { simp },
    { rw [h2, ←complex.of_real_inv, mul_comm, ←complex.real_smul,
          complex.smul_im, smul_eq_mul, ←inv_mul_lt_iff, inv_inv₀],
      { refine lt_trans _ (complex.neg_pi_lt_log_im _),
        simpa [two_mul] using real.pi_pos },
      { simp } },
    { rw [h2, ←complex.of_real_inv, mul_comm, ←complex.real_smul,
          complex.smul_im, smul_eq_mul, inv_mul_le_iff],
      { refine (complex.log_im_le_pi (x ^ 3 - 3 * x + 1)).trans _,
        simpa [two_mul] using real.pi_pos.le },
      { exact zero_lt_two } } }
end

-- P(X) : ℂ[X] Taylor expansion at α
example (p : polynomial ℂ) (α : ℂ) : ∃ (q : polynomial ℂ) (hq : q.nat_degree = p.nat_degree),
  p = q.sum (λ i a, a • (X - C α) ^ i) :=
begin
  use taylor α p,
  { sorry },
end

example : 321 = nat.of_digits 10 [1, 2, 3] :=
begin
  simp only [nat.of_digits_eq_foldr, add_zero, nat.cast_id, mul_zero, list.foldr],
  norm_num
end

example (m b : ℕ) (hp : 2 ≤ b) :
  ((nat.digits b m).map_with_index (λ i a, a * b ^ i)).sum = m :=
by rw [←nat.of_digits_eq_sum_map_with_index, nat.of_digits_digits]

-- every number `m` can be written as a sum over "digits" in base p
-- note, no hypothesis of `prime p` needed, just that `2 ≤ p`, which all primes are
example (m p : ℕ) (hp : 2 ≤ p) : ∃ (n : ℕ) (f : fin n → ℕ) (hf : ∀ i, f i < p),
  ∑ i, f i * p ^ (i : ℕ) = m :=
begin
  let l := nat.digits p m,
  refine ⟨l.length, λ i, l.nth_le i i.is_lt, λ _, nat.digits_lt_base hp (list.nth_le_mem _ _ _), _⟩,
  rw [←nat.of_digits_digits p m, nat.of_digits_eq_sum_map_with_index, ←list.sum_of_fn,
      list.map_with_index_eq_of_fn]
end

example (f : fin 3 → ℕ) (hf : f = ![5, 3, 6]) :
  320 = ∑ i, f i * 7 ^ (i : ℕ) :=
by norm_num [hf, fin.sum_univ_succ]

example : nat.digits 7 320 = [5, 3, 6] :=
by norm_num
