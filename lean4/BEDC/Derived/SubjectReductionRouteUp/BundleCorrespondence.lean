import BEDC.Derived.SubjectReductionRouteUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubjectReductionRouteUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SubjectReductionRouteBundleCorrespondence
    {beta application lambda pi bundle setup invocation consumer transport route provenance name
      betaApplication lambdaPi dischargeBundle : BHist} :
    UnaryHistory beta →
      UnaryHistory application →
        UnaryHistory lambda →
          UnaryHistory pi →
            Cont beta application betaApplication →
              Cont lambda pi lambdaPi →
                Cont betaApplication lambdaPi dischargeBundle →
                  subjectReductionRouteToEventFlow
                      (SubjectReductionRouteUp.mk beta application lambda pi bundle setup invocation
                        consumer transport route provenance name) =
                    subjectReductionRouteToEventFlow
                      (SubjectReductionRouteUp.mk beta application lambda pi bundle setup invocation
                        consumer transport route provenance name) →
                    UnaryHistory betaApplication ∧ UnaryHistory lambdaPi ∧
                      UnaryHistory dischargeBundle ∧ Cont beta application betaApplication ∧
                        Cont lambda pi lambdaPi ∧
                          Cont betaApplication lambdaPi dischargeBundle := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro betaUnary applicationUnary lambdaUnary piUnary betaApplicationRoute lambdaPiRoute
    dischargeRoute _eventFlowReadback
  have betaApplicationUnary : UnaryHistory betaApplication :=
    unary_cont_closed betaUnary applicationUnary betaApplicationRoute
  have lambdaPiUnary : UnaryHistory lambdaPi :=
    unary_cont_closed lambdaUnary piUnary lambdaPiRoute
  have dischargeUnary : UnaryHistory dischargeBundle :=
    unary_cont_closed betaApplicationUnary lambdaPiUnary dischargeRoute
  exact
    ⟨betaApplicationUnary, lambdaPiUnary, dischargeUnary, betaApplicationRoute,
      lambdaPiRoute, dischargeRoute⟩

end BEDC.Derived.SubjectReductionRouteUp
