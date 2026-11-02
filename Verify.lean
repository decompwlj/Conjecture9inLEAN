/-
Run `lake env lean Verify.lean` (after `lake build`).
Each `#print axioms` line lists the axioms a theorem depends on.  A complete proof depends only on
Lean's three standard axioms `propext`, `Classical.choice`, `Quot.sound`; the word `sorryAx` would
appear if any step were left unproved.
-/
import Theorem1inLean

open WLJ

-- The precise statements (printed so that they can be read and checked by a human).
#print WLJ.jump
#print WLJ.lval
#print WLJ.weight
#print WLJ.level
#print WLJ.ClassifiedByLevel
#print WLJ.levelCount
#print WLJ.Theorem1
#print WLJ.TripleSieveBound

#check @WLJ.lemma_1_1
#check @WLJ.decomposition
#check @WLJ.lval_eq_mul_prime_of_classifiedByLevel
#check @WLJ.levelCount_le
#check @WLJ.Table2.classifiedByLevel_P_small
#check @WLJ.theorem1_of_sieve

-- The axioms used by the proofs.
#print axioms WLJ.lemma_1_1
#print axioms WLJ.decomposition
#print axioms WLJ.lval_eq_mul_prime_of_classifiedByLevel
#print axioms WLJ.levelCount_le
#print axioms WLJ.Table2.classifiedByLevel_P_small
#print axioms WLJ.theorem1_of_sieve
