import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.WeierstrassApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem WeierstrassApproximationPolynomialHandoff [AskSetup] [PackageSetup]
    {interval functionRow errorRow polynomialRow samples modulus errorLedger transport
      routeConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory interval →
      UnaryHistory functionRow →
        UnaryHistory errorRow →
          UnaryHistory samples →
            UnaryHistory modulus →
              UnaryHistory transport →
                Cont interval functionRow samples →
                  Cont samples modulus polynomialRow →
                    Cont polynomialRow errorRow errorLedger →
                      Cont errorLedger transport routeConsumer →
                        PkgSig bundle polynomialRow pkg →
                          PkgSig bundle routeConsumer pkg →
                            UnaryHistory samples ∧
                              UnaryHistory polynomialRow ∧
                                UnaryHistory errorLedger ∧
                                  UnaryHistory routeConsumer ∧
                                    Cont interval functionRow samples ∧
                                      Cont samples modulus polynomialRow ∧
                                        Cont polynomialRow errorRow errorLedger ∧
                                          Cont errorLedger transport routeConsumer ∧
                                            PkgSig bundle polynomialRow pkg ∧
                                              PkgSig bundle routeConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro intervalUnary functionUnary errorUnary samplesUnary modulusUnary transportUnary
    sampleRoute polynomialRoute errorRoute consumerRoute polynomialPkg consumerPkg
  have routedSamplesUnary : UnaryHistory samples :=
    unary_cont_closed intervalUnary functionUnary sampleRoute
  have polynomialUnary : UnaryHistory polynomialRow :=
    unary_cont_closed routedSamplesUnary modulusUnary polynomialRoute
  have errorLedgerUnary : UnaryHistory errorLedger :=
    unary_cont_closed polynomialUnary errorUnary errorRoute
  have routeConsumerUnary : UnaryHistory routeConsumer :=
    unary_cont_closed errorLedgerUnary transportUnary consumerRoute
  exact
    ⟨routedSamplesUnary, polynomialUnary, errorLedgerUnary, routeConsumerUnary, sampleRoute,
      polynomialRoute, errorRoute, consumerRoute, polynomialPkg, consumerPkg⟩

end BEDC.Derived.WeierstrassApproximationUp
