import analysis.complex.polynomial
import data.polynomial.taylor

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

variables {R S : Type*}

instance polynomial.has_scalar_pi [semiring R] [has_scalar R S] :
  has_scalar (polynomial R) (R → S) :=
⟨λ p f x, eval x p • f x⟩

@[simp] lemma polynomial_smul_apply [semiring R] [has_scalar R S]
  (p : polynomial R) (f : R → S) (x : R) :
  (p • f) x = eval x p • f x := rfl

noncomputable instance polynomial.algebra_pi [comm_semiring R] :
  algebra (polynomial R) (R → R) :=
{ to_fun := λ p z, eval z p,
  map_one' := funext $ λ z, by simp,
  map_mul' := λ f g, funext $ λ z, by simp,
  map_zero' := funext $ λ z, by simp,
  map_add' := λ f g, funext $ λ z, by simp,
  commutes' := λ p f, funext $ λ z, mul_comm _ _,
  smul_def' := λ p f, funext $ λ z, by simp,
  ..polynomial.has_scalar_pi }

@[simp] lemma polynomial.algebra_map_pi_eq_eval [comm_semiring R] :
  (algebra_map (polynomial R) (R → R) : polynomial R → (R → R)) = λ p z, eval z p := rfl

-- f(X) = √(X ^ 3 − 3 X + 1),
-- which is a root of Y ^ 2 − (X ^ 3 − 3 X + 1), is an algebraic function
example : is_algebraic (polynomial ℂ) (λ x, complex.cpow (x ^ 3 - 3 • x + 1) (1 / 2)) :=
begin
  refine ⟨X ^ 2 - C (X ^ 3 - 3 • X + 1), _, _⟩,
  { intro H,
    replace H := congr_arg (eval 0) (congr_arg (eval 0) H),
    simpa using H },
  { ext1 x,
    suffices : ((x ^ 3 - 3 * x + 1) ^ (2 : ℂ)⁻¹) ^ 2 - (x ^ 3 - 3 * x + 1) = 0,
    { simpa only [_root_.map_add, map_pow, polynomial.aeval_bit1, polynomial.C_bit1, nat.cast_one,
                  nsmul_eq_mul, polynomial.algebra_map_pi_eq_eval, _root_.map_one, nat.cast_bit1,
                  polynomial.aeval_C, polynomial.aeval_X_pow, _root_.map_mul, _root_.map_sub,
                  eval_X, one_div] },
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

variables [semiring R] {p q : polynomial R}

lemma nat_degree_add_eq_left_of_nat_degree_lt (h : nat_degree q < nat_degree p) :
  nat_degree (p + q) = nat_degree p :=
nat_degree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt (degree_lt_degree h))

lemma nat_degree_add_eq_right_of_nat_degree_lt (h : nat_degree p < nat_degree q) :
  nat_degree (p + q) = nat_degree q :=
nat_degree_eq_of_degree_eq (degree_add_eq_right_of_degree_lt (degree_lt_degree h))

lemma degree_sum_eq_of_disjoint (f : S → polynomial R) (s : finset S)
  [decidable_pred (λ (i : S), f i ≠ 0)]
  (h : set.pairwise ↑(s.filter (λ i, f i ≠ 0)) (ne on (degree ∘ f))) :
  degree (∑ i in s, f i) = s.sup (λ i, degree (f i)) :=
begin
  classical,
  induction s using finset.induction_on with x s hx IH,
  { simp },
  { simp only [hx, finset.sum_insert, not_false_iff, finset.sup_insert],
    specialize IH (h.mono (λ _, by simp {contextual := tt})),
    rcases lt_trichotomy (degree (f x)) (degree (s.sum f)) with H|H|H,
    { rw [←IH, sup_eq_right.mpr H.le, degree_add_eq_right_of_degree_lt H] },
    { rcases s.eq_empty_or_nonempty with rfl|hs,
      { simp },
      obtain ⟨y, hy, hy'⟩ := finset.exists_mem_eq_sup s hs (λ i, degree (f i)),
      rw [IH, hy'] at H,
      by_cases hx0 : f x = 0,
      { simp [hx0, IH] },
      have hy0 : f y ≠ 0,
      { contrapose! H,
        simpa [H, degree_eq_bot] using hx0 },
      refine absurd H (h _ _ (λ H, hx _)),
      { simp [hx0] },
      { simp [hy, hy0] },
      { exact H.symm ▸ hy } },
    { rw [←IH, sup_eq_left.mpr H.le, degree_add_eq_left_of_degree_lt H] } }
end

lemma nat_degree_sum_eq_of_disjoint (f : S → polynomial R) (s : finset S)
  [decidable_pred (λ (i : S), f i ≠ 0)]
  (h : set.pairwise ↑(s.filter (λ i, f i ≠ 0)) (ne on (nat_degree ∘ f))) :
  nat_degree (∑ i in s, f i) = s.sup (λ i, nat_degree (f i)) :=
begin
  by_cases H : ∃ x ∈ s, f x ≠ 0,
  { obtain ⟨x, hx, hx'⟩ := H,
    have hs : s.nonempty := ⟨x, hx⟩,
    refine nat_degree_eq_of_degree_eq_some _,
    rw degree_sum_eq_of_disjoint,
    { rw [←finset.sup'_eq_sup hs, ←finset.sup'_eq_sup hs, finset.coe_sup', ←finset.sup'_eq_sup hs],
      refine le_antisymm _ _,
      { rw finset.sup'_le_iff,
        intros b hb,
        by_cases hb' : f b = 0,
        { simpa [hb'] using hs },
        rw degree_eq_nat_degree hb',
        exact finset.le_sup' _ hb },
      { rw finset.sup'_le_iff,
        intros b hb,
        simp only [finset.le_sup'_iff, exists_prop, function.comp_app],
        by_cases hb' : f b = 0,
        { refine ⟨x, hx, _⟩,
          contrapose! hx',
          simpa [hb', degree_eq_bot] using hx' },
        exact ⟨b, hb, (degree_eq_nat_degree hb').ge⟩ } },
    { exact h.imp (λ x y hxy hxy', hxy (nat_degree_eq_of_degree_eq hxy')) } },
  { push_neg at H,
    rw [finset.sum_eq_zero H, nat_degree_zero, eq_comm, show 0 = ⊥, from rfl,
        finset.sup_eq_bot_iff],
    intros x hx,
    simp [H x hx] }
end

lemma nat.choose_eq_zero_iff {n k : ℕ} :
  n.choose k = 0 ↔ n < k :=
begin
  refine ⟨_, nat.choose_eq_zero_of_lt⟩,
  induction n with n hn generalizing k,
  { cases k;
    simp },
  cases k,
  { simp },
  simp only [nat.choose_succ_succ, and_imp, add_eq_zero_iff],
  intros h _,
  exact nat.succ_lt_succ (hn h)
end

lemma finset.fold_ite {R}
  (op : R → R → R) [hc : is_commutative R op] [ha : is_associative R op]
  (b : R) (hb : op b b = b)
  (p : S → Prop) [decidable_pred p] (s : finset S) (f g : S → R) :
  finset.fold op b (λ i : S, ite (p i) (f i) (g i)) s =
  op (finset.fold op b f (s.filter p)) (finset.fold op b g (s.filter (λ i, ¬ p i))) :=
begin
  classical,
  induction s using finset.induction_on with x s hx IH,
  { simp [hb] },
  { simp only [finset.filter_congr_decidable, finset.fold_insert hx],
    split_ifs with h h,
    { have : x ∉ finset.filter p s,
      { simp [hx] },
      simp [finset.filter_insert, h, finset.fold_insert this, ha.assoc, IH] },
    { have : x ∉ finset.filter (λ i, ¬ p i) s,
      { simp [hx] },
      simp [finset.filter_insert, h, finset.fold_insert this, IH, ←ha.assoc, hc.comm] } }
end

example : is_idempotent ℕ (⊔) := by apply_instance

lemma finset.sup_ite [semilattice_sup R] [order_bot R]
  (p : S → Prop) [decidable_pred p] (s : finset S) (f g : S → R)  :
  finset.sup s (λ i : S, ite (p i) (f i) (g i)) =
    finset.sup (s.filter p) f ⊔ finset.sup (s.filter (λ i, ¬ p i)) g :=
finset.fold_ite _ _ sup_bot_eq _ _ _ _

lemma finset.fold_const {R} [decidable_eq S]
  (op : R → R → R) [hc : is_commutative R op] [ha : is_associative R op]
  (b : R) (s : finset S) (c : R) (h : op c (op b c) = op b c) :
  finset.fold op b (λ _, c) s = if s = ∅ then b else op b c :=
begin
  classical,
  induction s using finset.induction_on with x s hx IH,
  { simp },
  { simp only [finset.fold_insert hx, IH, if_false, finset.insert_ne_empty],
    split_ifs,
    { rw hc.comm },
    { exact h } }
end

lemma polynomial.nat_degree_hasse_deriv_le
  (p : polynomial R) (n : ℕ) :
  nat_degree (hasse_deriv n p) ≤ nat_degree p - n :=
begin
  classical,
  rw [hasse_deriv_apply, sum_def],
  have : ∀ i (r : R), nat_degree (monomial i r) = if r = 0 then 0 else i,
  { intros i r,
    by_cases hr : r = 0;
    simp [hr] },
  refine (nat_degree_sum_le _ _).trans _,
  simp_rw [function.comp, this], clear this,
  rw [finset.fold_ite _ _ (max_self _), finset.fold_const],
  { simp only [if_t_t, max_eq_right, zero_le', finset.fold_max_le, true_and, and_imp,
               tsub_le_iff_right, mem_support_iff, ne.def, finset.mem_filter],
    intros x hx hx',
    have hxp : x ≤ p.nat_degree := le_nat_degree_of_ne_zero hx,
    have hxn : n ≤ x,
    { contrapose! hx',
      simp [nat.choose_eq_zero_of_lt hx'] },
    rwa [tsub_add_cancel_of_le (hxn.trans hxp)] },
  { simp }
end

lemma polynomial.nat_degree_hasse_deriv
  [no_zero_smul_divisors ℕ R]
  (p : polynomial R) (n : ℕ) :
  nat_degree (hasse_deriv n p) = nat_degree p - n :=
begin
  refine le_antisymm (polynomial.nat_degree_hasse_deriv_le _ _) _,
  classical,
  rw [hasse_deriv_apply, sum_def],
  have : ∀ i (r : R), nat_degree (monomial i r) = if r = 0 then 0 else i,
  { intros i r,
    by_cases hr : r = 0;
    simp [hr] },
  rw [←finset.sum_filter_ne_zero, nat_degree_sum_eq_of_disjoint],
  { simp_rw this, clear this,
    rw [finset.sup_ite, finset.filter_filter],
    have hf : (λ (a : ℕ), (monomial (a - n)) (↑(a.choose n) * p.coeff a) ≠ 0 ∧
                ↑(a.choose n) * p.coeff a = 0) = λ a, false,
    { simp },
    simp_rw hf,
    simp only [finset.filter_false, finset.sup_empty, bot_sup_eq, finset.filter_filter,
                monomial_eq_zero_iff, ne.def, and_self, finset.filter_congr_decidable],
    clear hf,
    cases le_or_lt (p.nat_degree) n with hn hn,
    { rw tsub_eq_zero_of_le hn,
      exact nat.zero_le _ },
    rw finset.le_sup_iff,
    simp only [and_imp, monomial_eq_zero_iff, ne.def, and_self, finset.mem_filter],
    { refine ⟨p.nat_degree, _, le_rfl⟩,
      have hp : p ≠ 0,
      { rintro rfl,
        simpa using hn },
      -- this is where we use the `smul_eq_zero` from `no_zero_smul_divisors`
      simpa [←nsmul_eq_mul, hp, nat.choose_eq_zero_iff] using hn.le },
    { simpa using hn } },
  { refine λ x hx y hy hxy H, hxy _,
    dsimp at H,
    simp only [monomial_eq_zero_iff, mem_support_iff, ne.def, finset.mem_filter,
                finset.mem_coe] at hx hy,
    rw nat_degree_monomial _ _ hx.right at H,
    rw nat_degree_monomial _ _ hy.right at H,
    refine tsub_inj_left _ _ H,
    { contrapose! hx,
      simp [nat.choose_eq_zero_of_lt hx] },
    { contrapose! hy,
      simp [nat.choose_eq_zero_of_lt hy] } }
end

@[simp] lemma polynomial.nat_degree_taylor {R} [comm_ring R] (p : polynomial R) (r : R) :
  nat_degree (taylor r p) = nat_degree p :=
begin
  rcases eq_or_ne p 0 with rfl|hp,
  { simp },
  rw nat_degree_eq_support_max',
  { refine le_antisymm _ _,
    { rwa [ne.def, linear_map.map_eq_zero_iff _ (taylor_injective _)] },
    { rw finset.max'_le_iff,
      simp [taylor_coeff],
      intro y,
      contrapose!,
    },
    {  },
  },
  { rwa [ne.def, linear_map.map_eq_zero_iff _ (taylor_injective _)] },
end

#exit

-- P(X) : ℂ[X] Taylor expansion at α
example (p : polynomial ℂ) (α : ℂ) : ∃ (q : polynomial ℂ) (hq : q.nat_degree = p.nat_degree),
  p = q.sum (λ i a, a • (X - C α) ^ i) :=
begin
  use taylor α p,
  split,
  {  },
  -- set D : fin p.nat_degree → ℂ := λ i, (taylor α p).coeff i with hd,
  -- refine ⟨list.of_fn D, by simp, _⟩,
  -- simp only [hd, list.length_of_fn, list.nth_le_of_fn', list.length, list.nth_le, eq_self_iff_true,
  --            fin.eta],
  -- simp [taylor_coeff, hasse_deriv_apply, eval_sum],
  -- ext1 i,
  -- rw [sub_eq_add_neg, ←map_neg C α],
  -- simp only [coeff_smul, algebra.id.smul_eq_mul, finset_sum_coeff, coeff_X_add_C_pow],
  -- simp only [eval_sum, eval_monomial, taylor_coeff, hasse_deriv_apply],
end
