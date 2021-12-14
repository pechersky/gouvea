import field_theory.ratfunc

-- ring of integers ℤ
example : comm_ring ℤ := by apply_instance

-- field of fractions ℚ
noncomputable example : ℚ ≃+* fraction_ring ℤ := (fraction_ring.alg_equiv ℤ ℚ).symm.to_ring_equiv

attribute [simps] fraction_ring.alg_equiv

example : (fraction_ring.alg_equiv ℤ ℚ : fraction_ring ℤ → ℚ) =
  λ q, localization.lift_on q (λ n d, (n / d : ℚ))
    begin
      rintro a c ⟨b, hb⟩ ⟨d, hd⟩,
      rw localization.r_iff_exists,
      rintro ⟨⟨k, hk⟩, h⟩,
      rw mem_non_zero_divisors_iff_ne_zero at hb hd hk,
      simp only [set_like.coe_mk, coe_coe],
      rw div_eq_div_iff,
      { simpa [←int.cast_mul, hk] using h },
      { simpa only [int.cast_eq_zero, ne.def, coe_coe] using hb },
      { simpa only [int.cast_eq_zero, ne.def, coe_coe] using hd },
    end :=
begin
  ext x,
  induction x with n d a b c d h,
  { rw [fraction_ring.alg_equiv_apply, localization.lift_on_mk, localization.mk_eq_mk',
      is_localization.map_mk'],
    simp },
  { simp }
end

-- the equivalence between the two fields is what we expect
example : ((fraction_ring.alg_equiv ℤ ℚ).symm : ℚ → fraction_ring ℤ) =
  λ q, localization.mk q.num
    ⟨q.denom, mem_non_zero_divisors_iff_ne_zero.mpr (by simpa using q.pos.ne')⟩ :=
begin
  ext x,
  apply (fraction_ring.alg_equiv ℤ ℚ).injective,
  rw [alg_equiv.apply_symm_apply, fraction_ring.alg_equiv_apply, localization.mk_eq_mk',
      is_localization.map_mk'],
  simp
end
