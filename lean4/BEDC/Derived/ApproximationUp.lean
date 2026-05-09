import BEDC.Derived.ContinuousMapUp
import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.ApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.ContinuousMapUp
open BEDC.Derived.PolynomialUp

theorem ApproximationCarrierPacket_obligation_surface [AskSetup] [PackageSetup]
    {continuousSource continuousMap continuousTarget modulus continuousCert continuousDistance
      polynomialCandidate errorEndpoint errorLedger transportLedger provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuousMapCarrier continuousSource continuousMap continuousTarget modulus continuousCert
        continuousDistance ->
      PolynomialSingletonCarrier polynomialCandidate -> UnaryHistory transportLedger ->
        Cont continuousTarget polynomialCandidate errorEndpoint ->
          Cont errorEndpoint transportLedger errorLedger ->
            PkgSig bundle provenance pkg ->
              UnaryHistory continuousTarget ∧ PolynomialSingletonCarrier polynomialCandidate ∧
                UnaryHistory errorEndpoint ∧ UnaryHistory errorLedger ∧
                  hsame errorEndpoint (append continuousTarget polynomialCandidate) ∧
                    Cont errorEndpoint transportLedger errorLedger ∧
                      PkgSig bundle provenance pkg := by
  intro continuousCarrier polynomialCarrier transportUnary endpointRow ledgerRow provenancePkg
  have targetUnary : UnaryHistory continuousTarget :=
    continuousCarrier.left.right.left
  have polynomialUnary : UnaryHistory polynomialCandidate :=
    unary_transport unary_empty (hsame_symm polynomialCarrier)
  have endpointUnary : UnaryHistory errorEndpoint :=
    unary_cont_closed targetUnary polynomialUnary endpointRow
  have ledgerUnary : UnaryHistory errorLedger :=
    unary_cont_closed endpointUnary transportUnary ledgerRow
  exact And.intro targetUnary
    (And.intro polynomialCarrier
      (And.intro endpointUnary
        (And.intro ledgerUnary
          (And.intro endpointRow
            (And.intro ledgerRow provenancePkg)))))

end BEDC.Derived.ApproximationUp
