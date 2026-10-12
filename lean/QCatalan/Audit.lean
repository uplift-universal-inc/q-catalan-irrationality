import QCatalan.Main

/-!
# Public theorem and dependency audit

Run `./scripts/audit.sh` from the Lean project directory. The checker accepts only
Lean's standard logical axioms and requires a report for every query below.
-/

#check QCatalan.irrational_xi
#check QCatalan.irrational_qCatalan
#check QCatalan.irrational_qBeta_two

#print axioms QCatalan.irrational_xi
#print axioms QCatalan.irrational_qCatalan
#print axioms QCatalan.irrational_qBeta_two
#print axioms QCatalan.hasSum_xi
#print axioms QCatalan.hasSum_simplePole
#print axioms QCatalan.leading_coeff
#print axioms QCatalan.natDegree_Delta
#print axioms QCatalan.content_coeff
#print axioms QCatalan.DeltaR_cubic_decay
#print axioms QCatalan.frequently_ne_zero
#print axioms QCatalan.Generic.raw_cyclotomic_coeff_bound
#print axioms QCatalan.Generic.Delta_coeff_integerMonicFraction
#print axioms QCatalan.rawPK_coeff_den
#print axioms QCatalan.rawPK_frequently_ne_zero
#print axioms QCatalan.log_rawCK_le
#print axioms QCatalan.tendsto_pow_mul_rawEps_of_cost

-- These examples check that the public statement includes composite bases.
example : Irrational (QCatalan.xi 4) := QCatalan.irrational_xi (by norm_num)
example : Irrational (QCatalan.xi 6) := QCatalan.irrational_xi (by norm_num)
