import OmegaBalance
import OmegaBalance.Examples
import OmegaBalance.F3Examples
import OmegaBalance.FactorSumExamples

#print axioms OmegaBalance.bigOmega_zero
#print axioms OmegaBalance.bigOmega_one
#print axioms OmegaBalance.bigOmega_prime
#print axioms OmegaBalance.bigOmega_mul
#print axioms OmegaBalance.bigOmega_prime_pow
#print axioms OmegaBalance.neighborDiff_eq_zero_iff
#print axioms OmegaBalance.neighborDiff_pos_iff
#print axioms OmegaBalance.neighborDiff_neg_iff
#print axioms OmegaBalance.omegaDiff_eq_zero_iff
#print axioms OmegaBalance.isOmegaBalancedPrime_iff
#print axioms OmegaBalance.bigOmega_double_diff
#print axioms OmegaBalance.prime_mod_two_eq_one
#print axioms OmegaBalance.omegaDiff_eq_half_diff
#print axioms OmegaBalance.omegaDiff_prime_eq_half_diff
#print axioms OmegaBalance.isOmegaBalanced_iff_half
#print axioms OmegaBalance.omegaSum_eq_bigOmega_product
#print axioms OmegaBalance.omegaSum_eq_bigOmega_sq_sub_one
#print axioms OmegaBalance.omegaSum_add_omegaDiff
#print axioms OmegaBalance.omegaSum_sub_omegaDiff
#print axioms OmegaBalance.v3_two
#print axioms OmegaBalance.v3_three
#print axioms OmegaBalance.v3_four
#print axioms OmegaBalance.v3_eight
#print axioms OmegaBalance.v3_fourteen
#print axioms OmegaBalance.v3_six
#print axioms OmegaBalance.v3_twelve
#print axioms OmegaBalance.v3_eighteen
#print axioms OmegaBalance.v3_twenty_seven
#print axioms OmegaBalance.v3_twenty
#print axioms OmegaBalance.f3_three
#print axioms OmegaBalance.f3_five
#print axioms OmegaBalance.f3_seven
#print axioms OmegaBalance.f3_thirteen
#print axioms OmegaBalance.twin_five_seven_example
#print axioms OmegaBalance.twin_seventeen_nineteen_example
#print axioms OmegaBalance.exceptional_twin_three
#print axioms OmegaBalance.bigOmega_four
#print axioms OmegaBalance.bigOmega_six
#print axioms OmegaBalance.bigOmega_eight
#print axioms OmegaBalance.five_isOmegaBalancedPrime
#print axioms OmegaBalance.omegaDiff_twin_five_seven
#print axioms OmegaBalance.opposite_f3_not_sufficient_for_twins
#print axioms OmegaBalance.not_three_dvd_prime
#print axioms OmegaBalance.prime_mod_three
#print axioms OmegaBalance.twin_mod_three
#print axioms OmegaBalance.twin_mod_six
#print axioms OmegaBalance.six_dvd_twin_center
#print axioms OmegaBalance.twin_six_mul_form
#print axioms OmegaBalance.f3_of_mod_three_two
#print axioms OmegaBalance.f3_of_mod_three_one
#print axioms OmegaBalance.f3_ne_zero_of_prime
#print axioms OmegaBalance.f3_pos_iff_mod_three
#print axioms OmegaBalance.f3_neg_iff_mod_three
#print axioms OmegaBalance.f3_pair_values_of_mod_three
#print axioms OmegaBalance.f3_opposite_of_mod_three
#print axioms OmegaBalance.f3_twin_values
#print axioms OmegaBalance.f3_twin
#print axioms OmegaBalance.IsTwinPrime.f3_opposite
#print axioms OmegaBalance.f3_twin_signs
#print axioms OmegaBalance.f3_twin_abs_eq
#print axioms OmegaBalance.f3_twin_natAbs_eq
#print axioms OmegaBalance.f3_twin_mul_neg
#print axioms OmegaBalance.f3_eq_valuationDiff
#print axioms OmegaBalance.valuation_eq_padicValNat
#print axioms OmegaBalance.valuation_zero
#print axioms OmegaBalance.valuation_one
#print axioms OmegaBalance.valuation_eq_zero_of_not_dvd
#print axioms OmegaBalance.valuation_pos_of_dvd
#print axioms OmegaBalance.valuation_pos_iff_dvd
#print axioms OmegaBalance.valuation_mul
#print axioms OmegaBalance.valuation_prime_pow
#print axioms OmegaBalance.v3_zero
#print axioms OmegaBalance.v3_one
#print axioms OmegaBalance.v3_eq_zero_of_not_dvd
#print axioms OmegaBalance.v3_pos_of_dvd
#print axioms OmegaBalance.v3_pos_iff_dvd
#print axioms OmegaBalance.v3_mul
#print axioms OmegaBalance.v3_pow_three

#print axioms OmegaBalance.v3Int_nat
#print axioms OmegaBalance.v3Int_neg
#print axioms OmegaBalance.f3Int_nat
#print axioms OmegaBalance.f3Int_neg
#print axioms OmegaBalance.f3Int_neg_nat
#print axioms OmegaBalance.f3_of_mod_three_zero
#print axioms OmegaBalance.f3_eq_zero_iff_three_dvd
#print axioms OmegaBalance.f3_ne_zero_of_not_dvd
#print axioms OmegaBalance.f3_abs_eq_neighbor_sum
#print axioms OmegaBalance.f3_abs_eq_v3_sq_sub_one
#print axioms OmegaBalance.f3_sq
#print axioms OmegaBalance.v3_eq_one_of_mod_nine
#print axioms OmegaBalance.v3_quad_plus_one
#print axioms OmegaBalance.v3_quad_minus_one
#print axioms OmegaBalance.f3_cube_of_mod_three_one
#print axioms OmegaBalance.f3_cube_of_mod_three_two
#print axioms OmegaBalance.f3_cube

#print axioms OmegaBalance.f3Side_values
#print axioms OmegaBalance.f3_eq_side_mul_natAbs
#print axioms OmegaBalance.f3_center_pos
#print axioms OmegaBalance.f3_center_valuation
#print axioms OmegaBalance.v3Int_eq_padicValRat
#print axioms OmegaBalance.v3Int_add_ge_min
#print axioms OmegaBalance.v3Int_add_eq_min
#print axioms OmegaBalance.v3Int_sub_eq_min
#print axioms OmegaBalance.f3_adjusted_gap_valuation
#print axioms OmegaBalance.f3_reflection
#print axioms OmegaBalance.f3Side_mul
#print axioms OmegaBalance.f3_iterated_cube_pos
#print axioms OmegaBalance.f3_iterated_cube_neg
#print axioms OmegaBalance.v3_add_ge_min
#print axioms OmegaBalance.v3_add_eq_min
#print axioms OmegaBalance.f3_mul_depth

#print axioms OmegaBalance.f3Int_negative_five_example
#print axioms OmegaBalance.f3_square_five_example
#print axioms OmegaBalance.f3_cube_five_example
#print axioms OmegaBalance.f3_cube_seven_example
#print axioms OmegaBalance.f3_reflection_nine_example
#print axioms OmegaBalance.f3_multiply_unequal_example
#print axioms OmegaBalance.f3_iterated_cube_five_example
#print axioms OmegaBalance.f3_reflection_strict_boundary_example

-- FactorSum.lean
#print axioms OmegaBalance.primeFactorSum_zero
#print axioms OmegaBalance.primeFactorSum_one
#print axioms OmegaBalance.primeFactorSum_prime
#print axioms OmegaBalance.primeFactorSum_mul
#print axioms OmegaBalance.primeFactorSum_prime_pow
#print axioms OmegaBalance.primeFactorSum_of_factors
#print axioms OmegaBalance.bigOmega_of_factors
#print axioms OmegaBalance.primeFactorSumDiff_eq_zero_iff
#print axioms OmegaBalance.isPrimeFactorSumBalancedPrime_iff
#print axioms OmegaBalance.primeFactorSum_double_diff
#print axioms OmegaBalance.primeFactorSumDiff_eq_half_diff
#print axioms OmegaBalance.primeFactorSumDiff_prime_eq_half_diff
#print axioms OmegaBalance.primeFactorSumBalanced_iff_half
#print axioms OmegaBalance.primeFactorSum_center_iff
#print axioms OmegaBalance.primeFactorSum_cofactor_construction
#print axioms OmegaBalance.primeFactorSum_cofactor_defect
#print axioms OmegaBalance.doubleBalanced_sumBalanced
#print axioms OmegaBalance.doubleBalanced_omegaBalanced
#print axioms OmegaBalance.doubleBalanced_omegaSum
#print axioms OmegaBalance.doubleBalanced_twin_same_level

-- FactorSumArithmetic.lean
#print axioms OmegaBalance.factorList_prod_pos
#print axioms OmegaBalance.factorList_two_le_prod
#print axioms OmegaBalance.factorList_sum_le_prod
#print axioms OmegaBalance.primeFactorSum_le
#print axioms OmegaBalance.primeFactorSum_eq_self_iff
#print axioms OmegaBalance.primeFactorDefect_nonneg
#print axioms OmegaBalance.primeFactorDefect_eq_zero_iff
#print axioms OmegaBalance.primeFactorSum_odd_composite_bound
#print axioms OmegaBalance.bigOmega_eq_zero_iff
#print axioms OmegaBalance.bigOmega_eq_one_iff
#print axioms OmegaBalance.bigOmega_eq_two_factors
#print axioms OmegaBalance.bigOmega_eq_three_factors
#print axioms OmegaBalance.bigOmega_eq_four_factors
#print axioms OmegaBalance.factorList_sum_twos_parity
#print axioms OmegaBalance.primeFactorSum_parity
#print axioms OmegaBalance.primeFactorSum_odd_parity
#print axioms OmegaBalance.sumBalanced_count_valuation_parity
#print axioms OmegaBalance.valuation_eq_of_pow_dvd
#print axioms OmegaBalance.doubleBalanced_mod_eight

-- FactorSumExamples.lean
#print axioms OmegaBalance.sumFamily_prime_values_five
#print axioms OmegaBalance.sumBalanced_3615811
#print axioms OmegaBalance.sumBalanced_3615811_profile
#print axioms OmegaBalance.doubleBalanced_870404071
#print axioms OmegaBalance.doubleBalanced_748465063
#print axioms OmegaBalance.doubleBalanced_minimum_level
#print axioms OmegaBalance.sumBalanced_11
#print axioms OmegaBalance.sumBalanced_17
#print axioms OmegaBalance.sumBalanced_31

-- FactorSumFamily.lean
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

-- FactorSumFive.lean
#print axioms OmegaBalance.doubleBalanced_five_has_shape
#print axioms OmegaBalance.doubleBalanced_five_shape_iff
#print axioms OmegaBalance.doubleBalanced_five_mod_forty_eight
#print axioms OmegaBalance.doubleBalanced_five_not_twins
#print axioms OmegaBalance.doubleBalanced_twins_level_ge_six

-- FactorSumLowAux.lean
#print axioms OmegaBalance.sumBalanced_prime_halves
#print axioms OmegaBalance.even_factor_sum_split
#print axioms OmegaBalance.prime_consecutive_sum_bound
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
