import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.KolmogorovUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem KolmogorovBudgetMonotonicity_budget_transport
    {description budget budget' decoder trace trace' output output' accepted accepted' : BHist} :
    UnaryHistory description -> UnaryHistory budget -> UnaryHistory decoder ->
      hsame budget budget' -> Cont description budget trace -> Cont description budget' trace' ->
        Cont decoder trace output -> Cont decoder trace' output' -> Cont output budget accepted ->
          Cont output' budget' accepted' ->
            UnaryHistory budget' ∧ UnaryHistory trace ∧ UnaryHistory trace' ∧
              UnaryHistory output ∧ UnaryHistory output' ∧ UnaryHistory accepted ∧
                UnaryHistory accepted' ∧ hsame trace trace' ∧ hsame output output' ∧
                  hsame accepted accepted' := by
  intro descriptionUnary budgetUnary decoderUnary sameBudget traceRow traceRow' outputRow outputRow'
  intro acceptedRow acceptedRow'
  have budgetUnary' : UnaryHistory budget' :=
    unary_transport budgetUnary sameBudget
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed descriptionUnary budgetUnary traceRow
  have traceUnary' : UnaryHistory trace' :=
    unary_cont_closed descriptionUnary budgetUnary' traceRow'
  have outputUnary : UnaryHistory output :=
    unary_cont_closed decoderUnary traceUnary outputRow
  have outputUnary' : UnaryHistory output' :=
    unary_cont_closed decoderUnary traceUnary' outputRow'
  have acceptedUnary : UnaryHistory accepted :=
    unary_cont_closed outputUnary budgetUnary acceptedRow
  have acceptedUnary' : UnaryHistory accepted' :=
    unary_cont_closed outputUnary' budgetUnary' acceptedRow'
  have traceSame : hsame trace trace' :=
    cont_respects_hsame (hsame_refl description) sameBudget traceRow traceRow'
  have outputSame : hsame output output' :=
    cont_respects_hsame (hsame_refl decoder) traceSame outputRow outputRow'
  have acceptedSame : hsame accepted accepted' :=
    cont_respects_hsame outputSame sameBudget acceptedRow acceptedRow'
  exact
    ⟨budgetUnary', traceUnary, traceUnary', outputUnary, outputUnary', acceptedUnary,
      acceptedUnary', traceSame, outputSame, acceptedSame⟩

theorem KolmogorovPrefixFreeCarrier_obligation_surface
    {description budget decoder trace output readback fixedClassifier carrier : BHist} :
    UnaryHistory description -> UnaryHistory budget -> UnaryHistory decoder -> UnaryHistory output ->
      Cont description budget fixedClassifier -> Cont decoder description trace ->
        Cont trace output readback -> Cont fixedClassifier readback carrier ->
          UnaryHistory fixedClassifier ∧ UnaryHistory trace ∧ UnaryHistory readback ∧
            UnaryHistory carrier ∧ hsame fixedClassifier (append description budget) ∧
              hsame trace (append decoder description) ∧ hsame readback (append trace output) ∧
                hsame carrier (append fixedClassifier readback) := by
  intro descriptionUnary budgetUnary decoderUnary outputUnary fixedClassifierRow traceRow
  intro readbackRow carrierRow
  have fixedClassifierUnary : UnaryHistory fixedClassifier :=
    unary_cont_closed descriptionUnary budgetUnary fixedClassifierRow
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed decoderUnary descriptionUnary traceRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed traceUnary outputUnary readbackRow
  have carrierUnary : UnaryHistory carrier :=
    unary_cont_closed fixedClassifierUnary readbackUnary carrierRow
  exact
    ⟨fixedClassifierUnary, traceUnary, readbackUnary, carrierUnary, fixedClassifierRow,
      traceRow, readbackRow, carrierRow⟩

end BEDC.Derived.KolmogorovUp
