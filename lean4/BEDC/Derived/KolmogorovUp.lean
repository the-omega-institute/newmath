import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.KolmogorovUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem KolmogorovPrefixFreeCarrierObligation_finite_surface
    {description budget decoder trace readback witness zeroBranch oneBranch : BHist} :
    UnaryHistory description -> UnaryHistory budget -> UnaryHistory decoder ->
      Cont decoder description trace -> Cont trace budget readback ->
        Cont description readback witness ->
          Cont description (BHist.e0 BHist.Empty) zeroBranch ->
            Cont description (BHist.e1 BHist.Empty) oneBranch ->
              UnaryHistory trace ∧ UnaryHistory readback ∧ UnaryHistory witness ∧
                hsame trace (append decoder description) ∧
                  hsame readback (append trace budget) ∧
                    hsame witness (append description readback) ∧
                      (hsame zeroBranch oneBranch -> False) := by
  intro descriptionUnary budgetUnary decoderUnary traceRow readbackRow witnessRow zeroBranchRow
  intro oneBranchRow
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed decoderUnary descriptionUnary traceRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed traceUnary budgetUnary readbackRow
  have witnessUnary : UnaryHistory witness :=
    unary_cont_closed descriptionUnary readbackUnary witnessRow
  have branchDisjoint : hsame zeroBranch oneBranch -> False := by
    intro sameBranch
    have impossible :
        append description (BHist.e0 BHist.Empty) =
          append description (BHist.e1 BHist.Empty) :=
      zeroBranchRow.symm.trans (sameBranch.trans oneBranchRow)
    cases impossible
  exact
    ⟨traceUnary, readbackUnary, witnessUnary, traceRow, readbackRow, witnessRow,
      branchDisjoint⟩

end BEDC.Derived.KolmogorovUp
