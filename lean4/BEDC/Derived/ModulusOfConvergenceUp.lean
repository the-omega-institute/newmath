import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ModulusOfConvergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ModulusOfConvergenceCarrier [AskSetup] [PackageSetup]
    (precision selector modulus schedule witness ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory selector ∧ UnaryHistory modulus ∧
    UnaryHistory schedule ∧ UnaryHistory witness ∧ UnaryHistory ledger ∧
      UnaryHistory provenance ∧ Cont precision selector modulus ∧
        Cont modulus schedule witness ∧ Cont witness ledger provenance ∧
          PkgSig bundle provenance pkg

theorem ModulusOfConvergenceCarrier_composition_stability [AskSetup] [PackageSetup]
    {precision selector modulus schedule witness ledger provenance precision' selector' modulus'
      schedule' witness' ledger' provenance' : BHist}
    {bundle bundle' : ProbeBundle ProbeName} {pkg pkg' : Pkg} :
    ModulusOfConvergenceCarrier precision selector modulus schedule witness ledger provenance
        bundle pkg ->
      ModulusOfConvergenceCarrier precision' selector' modulus' schedule' witness' ledger'
        provenance' bundle' pkg' ->
        exists joined : BHist, Cont provenance precision' joined ∧ UnaryHistory joined := by
  intro leftCarrier rightCarrier
  cases leftCarrier with
  | intro _precisionUnary leftRest =>
      cases leftRest with
      | intro _selectorUnary leftRest =>
          cases leftRest with
          | intro _modulusUnary leftRest =>
              cases leftRest with
              | intro _scheduleUnary leftRest =>
                  cases leftRest with
                  | intro _witnessUnary leftRest =>
                      cases leftRest with
                      | intro _ledgerUnary leftRest =>
                          cases leftRest with
                          | intro provenanceUnary _leftRows =>
                              cases rightCarrier with
                              | intro precisionUnary' _rightRest =>
                                  let joined := append provenance precision'
                                  have joinedRow : Cont provenance precision' joined := by
                                    rfl
                                  have joinedUnary : UnaryHistory joined :=
                                    unary_repetition_closed_under_continuation provenanceUnary
                                      precisionUnary' joinedRow
                                  exact ⟨joined, joinedRow, joinedUnary⟩

end BEDC.Derived.ModulusOfConvergenceUp
