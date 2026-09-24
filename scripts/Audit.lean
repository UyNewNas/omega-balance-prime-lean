import OmegaBalance

namespace OmegaBalance

-- Basic.lean
#print axioms OmegaBalance.bigOmega_zero
#print axioms OmegaBalance.bigOmega_one
#print axioms OmegaBalance.bigOmega_prime
#print axioms OmegaBalance.bigOmega_mul
#print axioms OmegaBalance.bigOmega_prime_pow
#print axioms OmegaBalance.omegaDiff_eq_zero_iff
#print axioms OmegaBalance.isOmegaBalancedPrime_iff
#print axioms OmegaBalance.omegaDiff_eq_half_diff
#print axioms OmegaBalance.isOmegaBalanced_iff_half
#print axioms OmegaBalance.omegaSum_eq_bigOmega_product
#print axioms OmegaBalance.omegaSum_eq_bigOmega_sq_sub_one
#print axioms OmegaBalance.omegaDiff_prime_eq_half_diff
#print axioms OmegaBalance.omegaSum_add_omegaDiff
#print axioms OmegaBalance.omegaSum_sub_omegaDiff

-- Valuation.lean
#print axioms OmegaBalance.valuation_pos_iff_dvd
#print axioms OmegaBalance.valuation_mul
#print axioms OmegaBalance.valuation_prime_pow

-- F3.lean
#print axioms OmegaBalance.f3_opposite_of_mod_three
#print axioms OmegaBalance.f3_twin
#print axioms OmegaBalance.f3_twin_values
#print axioms OmegaBalance.f3_twin_signs
#print axioms OmegaBalance.f3_twin_abs_eq
#print axioms OmegaBalance.f3_twin_natAbs_eq
#print axioms OmegaBalance.f3_twin_mul_neg
#print axioms OmegaBalance.twin_mod_six
#print axioms OmegaBalance.six_dvd_twin_center
#print axioms OmegaBalance.twin_six_mul_form
#print axioms OmegaBalance.f3_ne_zero_of_prime
#print axioms OmegaBalance.f3_pos_iff_mod_three
#print axioms OmegaBalance.f3_neg_iff_mod_three

-- F3Extension.lean
#print axioms OmegaBalance.f3Int_nat
#print axioms OmegaBalance.f3Int_neg
#print axioms OmegaBalance.f3_eq_zero_iff_three_dvd
#print axioms OmegaBalance.f3_sq
#print axioms OmegaBalance.f3_cube

-- F3Arithmetic.lean
#print axioms OmegaBalance.f3_iterated_cube_pos
#print axioms OmegaBalance.f3_iterated_cube_neg
#print axioms OmegaBalance.f3_mul_depth
#print axioms OmegaBalance.f3Side_mul
#print axioms OmegaBalance.f3_adjusted_gap_valuation
#print axioms OmegaBalance.f3_reflection

-- F3Examples.lean / Examples.lean (imported transitively in verification targets)
#print axioms OmegaBalance.five_isOmegaBalancedPrime
#print axioms OmegaBalance.twin_seventeen_nineteen_example
#print axioms OmegaBalance.f3_three
#print axioms OmegaBalance.f3_five
#print axioms OmegaBalance.exceptional_twin_three
#print axioms OmegaBalance.opposite_f3_not_sufficient_for_twins
#print axioms OmegaBalance.omegaDiff_twin_five_seven

-- F3Powers.lean
#print axioms OmegaBalance.v3_pow_sub_one
#print axioms OmegaBalance.f3_pow_depth
#print axioms OmegaBalance.f3Side_pow
#print axioms OmegaBalance.f3_pow

-- F3Rational.lean
#print axioms OmegaBalance.f3Rat_int
#print axioms OmegaBalance.f3Rat_nat
#print axioms OmegaBalance.f3Rat_neg
#print axioms OmegaBalance.f3Rat_eq_cayley_valuation
#print axioms OmegaBalance.f3Star_comm
#print axioms OmegaBalance.f3Star_gt_one
#print axioms OmegaBalance.f3Star_add_one
#print axioms OmegaBalance.f3Star_sub_one
#print axioms OmegaBalance.f3Rat_star
#print axioms OmegaBalance.f3Rat_star_of_gt_one
#print axioms OmegaBalance.f3Cayley_gt_one
#print axioms OmegaBalance.f3Cayley_involution
#print axioms OmegaBalance.f3Cayley_injective
#print axioms OmegaBalance.f3Cayley_star
#print axioms OmegaBalance.f3Star_assoc

-- F3SumProduct.lean
#print axioms OmegaBalance.f3_positive_level
#print axioms OmegaBalance.f3_negative_level
#print axioms OmegaBalance.pow_three_dvd_of_le_v3
#print axioms OmegaBalance.v3_exact_factor
#print axioms OmegaBalance.f3_opposite_sum_product
#print axioms OmegaBalance.f3_opposite_sum_product_min
#print axioms OmegaBalance.f3_twin_product_of_mod
#print axioms OmegaBalance.f3_twin_product
#print axioms OmegaBalance.f3_product_refined_gap
#print axioms OmegaBalance.f3_product_gap_dichotomy

-- F3Order.lean
#print axioms OmegaBalance.nat_pow_zmod_eq_one_iff
#print axioms OmegaBalance.f3_pow_zmod_neg_iff
#print axioms OmegaBalance.v3_power_sub_one_from_depth
#print axioms OmegaBalance.f3_pow_zmod_pos_iff
#print axioms OmegaBalance.f3_orderOf_neg
#print axioms OmegaBalance.f3_orderOf_pos
#print axioms OmegaBalance.f3_orderOf
#print axioms OmegaBalance.f3_twin_orderOf

-- F3Coordinates.lean
#print axioms OmegaBalance.f3Unit_mul
#print axioms OmegaBalance.f3Unit_sub_one_ne_zero
#print axioms OmegaBalance.f3Unit_depth
#print axioms OmegaBalance.v3Int_mul
#print axioms OmegaBalance.v3Int_three_pow
#print axioms OmegaBalance.f3_same_level_cancellation
#print axioms OmegaBalance.f3_same_level_rises_iff

-- F3Primitive.lean
#print axioms OmegaBalance.f3_eq_one_iff_order_nine
#print axioms OmegaBalance.f3_eq_one_iff_maximal_order_tower

-- F3Finite.lean
#print axioms OmegaBalance.sum_initial_indicator
#print axioms OmegaBalance.v3Trunc_eq_min
#print axioms OmegaBalance.v3Trunc_zero
#print axioms OmegaBalance.v3Trunc_translate
#print axioms OmegaBalance.f3Trunc_periodic
#print axioms OmegaBalance.f3Trunc_eq_clipped
#print axioms OmegaBalance.f3Trunc_eq_f3
#print axioms OmegaBalance.f3_sum_range

-- FactorSum.lean
#print axioms OmegaBalance.primeFactorSum_zero
#print axioms OmegaBalance.primeFactorSum_one
#print axioms OmegaBalance.primeFactorSum_prime
#print axioms OmegaBalance.primeFactorSum_mul
#print axioms OmegaBalance.primeFactorSum_prime_pow
#print axioms OmegaBalance.primeFactorSumDiff_eq_zero_iff
#print axioms OmegaBalance.primeFactorSumDiff_eq_half_diff
#print axioms OmegaBalance.primeFactorSumBalanced_iff_half
#print axioms OmegaBalance.primeFactorSum_cofactor_construction
#print axioms OmegaBalance.primeFactorSum_cofactor_defect
#print axioms OmegaBalance.primeFactorSum_of_factors

-- FactorSumArithmetic.lean
#print axioms OmegaBalance.primeFactorSum_le
#print axioms OmegaBalance.primeFactorSum_eq_self_iff
#print axioms OmegaBalance.primeFactorDefect_eq_zero_iff
#print axioms OmegaBalance.primeFactorSum_parity
#print axioms OmegaBalance.sumBalanced_count_valuation_parity

-- FactorSumParity.lean
#print axioms OmegaBalance.doubleBalanced_two_adic_profile
#print axioms OmegaBalance.doubleBalanced_mod_eight
#print axioms OmegaBalance.doubleBalanced_common_sum_parity

-- FactorSumExamples.lean
#print axioms OmegaBalance.sumFamily_prime_values_five
#print axioms OmegaBalance.sumBalanced_3615811_profile
#print axioms OmegaBalance.doubleBalanced_870404071
#print axioms OmegaBalance.doubleBalanced_870404071_profile
#print axioms OmegaBalance.doubleBalanced_748465063
#print axioms OmegaBalance.doubleBalanced_minimum_level
#print axioms OmegaBalance.sumBalanced_11
#print axioms OmegaBalance.sumBalanced_17
#print axioms OmegaBalance.sumBalanced_31

-- FactorSumFamily.lean
#print axioms OmegaBalance.sumFamily_B_eq_A_add_one
#print axioms OmegaBalance.sumFamily_B_sub_A_eq_one
#print axioms OmegaBalance.sumFamily_Q_inverse
#print axioms OmegaBalance.sumFamily_R_inverse
#print axioms OmegaBalance.sumFamily_Q_sub_R
#print axioms OmegaBalance.nppFamily_mod_three_obstruction
#print axioms OmegaBalance.nppFamily_three_dvd_center_of_linear_primes
#print axioms OmegaBalance.nppFamily_no_prime_center
#print axioms OmegaBalance.sumFamily_adjacent
#print axioms OmegaBalance.sumFamily_center_eq
#print axioms OmegaBalance.sumFamily_pred
#print axioms OmegaBalance.sumFamily_succ
#print axioms OmegaBalance.sumFamily_factor_sum_identity
#print axioms OmegaBalance.sumFamily_left_profile
#print axioms OmegaBalance.sumFamily_right_profile
#print axioms OmegaBalance.sumFamily_balanced
#print axioms OmegaBalance.sumFamily_five_primes
#print axioms OmegaBalance.sumFamily_omegaSum_eq_nine
#print axioms OmegaBalance.sumFamily_omegaDiff_eq_neg_one
#print axioms OmegaBalance.sumFamily_not_omegaBalanced
#print axioms OmegaBalance.sumFamily_defect_identity
#print axioms OmegaBalance.sumFamily_balanced_iff_defect
#print axioms OmegaBalance.sumCofactor_inverse_identity
#print axioms OmegaBalance.doubleFactorPair_identity
#print axioms OmegaBalance.doubleFactorPair_iff
#print axioms OmegaBalance.sumFamily_mod_two_table
#print axioms OmegaBalance.sumFamily_mod_three_table
#print axioms OmegaBalance.sumFamily_mod_five_table
#print axioms OmegaBalance.sumFamily_mod_seven_table
#print axioms OmegaBalance.sumFamily_small_prime_admissible

-- FactorSumFive.lean
#print axioms OmegaBalance.doubleBalanced_five_has_shape
#print axioms OmegaBalance.doubleBalanced_five_shape_iff
#print axioms OmegaBalance.doubleBalanced_five_signed_gap
#print axioms OmegaBalance.doubleBalanced_five_gap_natAbs
#print axioms OmegaBalance.doubleBalanced_five_of_factor_pair_pos
#print axioms OmegaBalance.doubleBalanced_five_of_factor_pair_neg
#print axioms OmegaBalance.doubleBalanced_five_mod_forty_eight
#print axioms OmegaBalance.doubleBalanced_five_not_twins
#print axioms OmegaBalance.doubleBalanced_twins_level_ge_six

-- FactorSumLowAux.lean
#print axioms OmegaBalance.sumBalanced_prime_halves
#print axioms OmegaBalance.even_factor_sum_split
#print axioms OmegaBalance.prime_consecutive_sum_bound
#print axioms OmegaBalance.prime_consecutive_sum_eq_five_six
#print axioms OmegaBalance.sumBalanced_halves_nonprime_of_ne_eleven
#print axioms OmegaBalance.even_omega_two_shape
#print axioms OmegaBalance.even_omega_three_shape
#print axioms OmegaBalance.even_omega_four_even_sum_shape
#print axioms OmegaBalance.three_dvd_adjacent_prime_sum
#print axioms OmegaBalance.adjacent_not_common_dvd
#print axioms OmegaBalance.two_odd_factor_gap
#print axioms OmegaBalance.four_odd_factor_gap
#print axioms OmegaBalance.low_pair_six_bound
#print axioms OmegaBalance.low_pair_twelve_bound
#print axioms OmegaBalance.small_sum_balanced_low_count

-- FactorSumLowCount.lean
#print axioms OmegaBalance.sumPair_two_three_bound
#print axioms OmegaBalance.sumPair_two_four_bound
#print axioms OmegaBalance.sumPair_three_three_impossible
#print axioms OmegaBalance.sumBalanced_low_count_bound
#print axioms OmegaBalance.sumBalanced_total_le_eight_iff
#print axioms OmegaBalance.sumBalanced_total_ge_nine
#print axioms OmegaBalance.infinite_sumBalanced_level_ge_nine
#print axioms OmegaBalance.sumFamilyCenter_strictMono
#print axioms OmegaBalance.infinite_sumFamily_implies_level_nine

-- FactorSumStructure.lean
#print axioms OmegaBalance.prime_three_le_of_dvd_odd
#print axioms OmegaBalance.prime_five_le_of_dvd_odd
#print axioms OmegaBalance.doubleBalanced_split
#print axioms OmegaBalance.triple_factor_gap_bound
#print axioms OmegaBalance.doubleBalanced_level_ge_five
#print axioms OmegaBalance.doubleBalanced_five_of_shape
#print axioms OmegaBalance.doubleFiveShape_mod_forty_eight
#print axioms OmegaBalance.doubleFiveShape_not_twins
#print axioms OmegaBalance.quadruple_factor_gap_bound

-- Preserved concurrent F3 extension from master d6ad217.
#print axioms OmegaBalance.v3_eq_padic
#print axioms OmegaBalance.three_not_dvd_pow
#print axioms OmegaBalance.v3_pow_sub_one
#print axioms OmegaBalance.f3_pow_depth
#print axioms OmegaBalance.f3Side_pow
#print axioms OmegaBalance.f3_pow
#print axioms OmegaBalance.f3Rat_int
#print axioms OmegaBalance.f3Rat_nat
#print axioms OmegaBalance.f3Rat_neg
#print axioms OmegaBalance.f3Rat_eq_cayley_valuation
#print axioms OmegaBalance.f3Star_comm
#print axioms OmegaBalance.f3Star_gt_one
#print axioms OmegaBalance.f3Star_add_one
#print axioms OmegaBalance.f3Star_sub_one
#print axioms OmegaBalance.f3Rat_star
#print axioms OmegaBalance.f3Rat_star_of_gt_one
#print axioms OmegaBalance.f3Cayley_gt_one
#print axioms OmegaBalance.f3Cayley_involution
#print axioms OmegaBalance.f3Cayley_injective
#print axioms OmegaBalance.f3Cayley_star
#print axioms OmegaBalance.f3Star_assoc
#print axioms OmegaBalance.f3_positive_level
#print axioms OmegaBalance.f3_negative_level
#print axioms OmegaBalance.pow_three_dvd_of_le_v3
#print axioms OmegaBalance.v3_exact_factor
#print axioms OmegaBalance.f3_opposite_sum_product
#print axioms OmegaBalance.f3_opposite_sum_product_min
#print axioms OmegaBalance.f3_twin_product_of_mod
#print axioms OmegaBalance.f3_twin_product
#print axioms OmegaBalance.f3_product_refined_gap
#print axioms OmegaBalance.f3_product_gap_dichotomy
#print axioms OmegaBalance.nat_pow_zmod_eq_one_iff
#print axioms OmegaBalance.f3_pow_zmod_neg_iff
#print axioms OmegaBalance.v3_power_sub_one_from_depth
#print axioms OmegaBalance.f3_pow_zmod_pos_iff
#print axioms OmegaBalance.f3_orderOf_neg
#print axioms OmegaBalance.f3_orderOf_pos
#print axioms OmegaBalance.f3_orderOf
#print axioms OmegaBalance.f3_twin_orderOf
#print axioms OmegaBalance.f3Unit_mul
#print axioms OmegaBalance.f3Unit_sub_one_ne_zero
#print axioms OmegaBalance.f3Unit_depth
#print axioms OmegaBalance.v3Int_mul
#print axioms OmegaBalance.v3Int_three_pow
#print axioms OmegaBalance.f3_same_level_cancellation
#print axioms OmegaBalance.f3_same_level_rises_iff
#print axioms OmegaBalance.f3_eq_one_iff_order_nine
#print axioms OmegaBalance.f3_eq_one_iff_maximal_order_tower
#print axioms OmegaBalance.sum_initial_indicator
#print axioms OmegaBalance.v3Trunc_eq_min
#print axioms OmegaBalance.v3Trunc_zero
#print axioms OmegaBalance.v3Trunc_translate
#print axioms OmegaBalance.f3Trunc_periodic
#print axioms OmegaBalance.f3Trunc_eq_clipped
#print axioms OmegaBalance.f3Trunc_eq_f3
#print axioms OmegaBalance.f3_sum_range
#print axioms OmegaBalance.f3_eleven
#print axioms OmegaBalance.f3_thirty_five
#print axioms OmegaBalance.f3_seventy_seven
#print axioms OmegaBalance.f3_no_scalar_mul_rule
#print axioms OmegaBalance.f3_general_power_example
#print axioms OmegaBalance.f3_order_five_example
#print axioms OmegaBalance.f3_twin_order_example
#print axioms OmegaBalance.f3_primitive_five_example
#print axioms OmegaBalance.f3_one_eighty_one
#print axioms OmegaBalance.f3_refined_gap_boundary_example
#print axioms OmegaBalance.f3_sum_product_branch_example
#print axioms OmegaBalance.f3_star_rational_example
#print axioms OmegaBalance.f3_star_integer_example
#print axioms OmegaBalance.f3_cutoff_zero_boundary
#print axioms OmegaBalance.f3_telescoping_example

-- FactorSumSmallCertificates.lean
#print axioms OmegaBalance.smallSumCertificates_cover
#print axioms OmegaBalance.smallSumCertificates_valid

-- Cofactor necessity and reversible recovery.
#print axioms OmegaBalance.sumCofactor_coprime
#print axioms OmegaBalance.sumCofactor_ne
#print axioms OmegaBalance.sumCofactor_divisibility
#print axioms OmegaBalance.sumCofactor_inverse_iff
#print axioms OmegaBalance.sumCofactor_sign
#print axioms OmegaBalance.sumCofactor_opposite_parity
#print axioms OmegaBalance.sumCofactor_even_sum_difference
#print axioms OmegaBalance.sumCofactor_recover_balanced
#print axioms OmegaBalance.doubleFactorPair_recover

-- FactorSumAdmissibility.lean
#print axioms OmegaBalance.sumFamilyPolyU_eval_natCast
#print axioms OmegaBalance.sumFamilyPolyV_eval_natCast
#print axioms OmegaBalance.sumFamilyPolyQ_eval_natCast
#print axioms OmegaBalance.sumFamilyPolyR_eval_natCast
#print axioms OmegaBalance.sumFamilyPolyCenter_eval_natCast
#print axioms OmegaBalance.sumFamilyProductPoly_eval_natCast
#print axioms OmegaBalance.sumFamilyProductPoly_natDegree_le_nine
#print axioms OmegaBalance.sumFamilyProductPoly_ne_zero_of_prime
#print axioms OmegaBalance.sumFamily_large_prime_admissible
#print axioms OmegaBalance.sumFamily_prime_admissible

end OmegaBalance