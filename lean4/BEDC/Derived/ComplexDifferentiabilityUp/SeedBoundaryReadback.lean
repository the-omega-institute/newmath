import BEDC.Derived.ComplexDifferentiabilityUp

namespace BEDC.Derived.ComplexDifferentiabilityUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexDiffUp

theorem ComplexDifferentiabilitySeedBoundary_quotient_derivative_readback
    {f z fp h q q' : BHist} :
    CplxDiffAt f z fp -> CplxDiffQuot f z h q -> Cont f h q' ->
      hsame fp q' ∧ CplxNonZero h ∧ UnaryHistory h ∧ UnaryHistory q' := by
  intro diff quotient continuation
  have quotientRows := CplxDiffQuot_step_unary quotient
  have sameQFp : hsame q fp := diff.right.right.right.right quotient
  have sameQQ' : hsame q q' :=
    cont_deterministic quotientRows.right.right continuation
  have q'Unary : UnaryHistory q' :=
    unary_transport quotientRows.right.left sameQQ'
  exact And.intro (hsame_trans (hsame_symm sameQFp) sameQQ')
    (And.intro quotient.right.right.left
      (And.intro quotientRows.left q'Unary))

end BEDC.Derived.ComplexDifferentiabilityUp
