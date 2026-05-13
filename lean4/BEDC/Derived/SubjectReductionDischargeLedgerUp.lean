import BEDC.Derived.SubjectReductionDischargeLedgerUp.TasteGate
import BEDC.FKernel.Cont.Units

namespace BEDC.Derived.SubjectReductionDischargeLedgerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem SubjectReductionDischargeLedgerRouteExhaustion
    (x : SubjectReductionDischargeLedgerUp) :
    ∃ beta appArg lambdaDomain piDomain route transport replay provenance name : BHist,
      x = SubjectReductionDischargeLedgerUp.mk beta appArg lambdaDomain piDomain route
          transport replay provenance name ∧
        Cont BHist.Empty beta beta ∧ Cont BHist.Empty appArg appArg ∧
          Cont BHist.Empty lambdaDomain lambdaDomain ∧
            Cont BHist.Empty piDomain piDomain ∧
              hsame route (append BHist.Empty route) := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  cases x with
  | mk beta appArg lambdaDomain piDomain route transport replay provenance name =>
      exact
        ⟨beta, appArg, lambdaDomain, piDomain, route, transport, replay, provenance, name,
          rfl, cont_left_unit beta, cont_left_unit appArg, cont_left_unit lambdaDomain,
          cont_left_unit piDomain, (append_empty_left route).symm⟩

end BEDC.Derived.SubjectReductionDischargeLedgerUp
