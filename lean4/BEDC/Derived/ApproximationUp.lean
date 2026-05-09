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

theorem ApproximationFiniteErrorLedger_carrier_surface {continuousSource map target modulus cert
    distance polynomialCandidate sourceEndpoint polynomialEndpoint errorEndpoint errorLedger
    provenance : BHist} :
    ContinuousMapCarrier continuousSource map target modulus cert distance ->
      PolynomialSingletonCarrier polynomialCandidate ->
        UnaryHistory sourceEndpoint ->
          UnaryHistory polynomialEndpoint ->
            Cont continuousSource polynomialCandidate errorLedger ->
              Cont sourceEndpoint polynomialEndpoint errorEndpoint ->
                hsame provenance errorLedger ->
                  UnaryHistory errorLedger ∧ UnaryHistory errorEndpoint ∧
                    hsame errorLedger (append continuousSource polynomialCandidate) ∧
                      hsame errorEndpoint (append sourceEndpoint polynomialEndpoint) ∧
                        hsame provenance errorLedger := by
  intro continuousCarrier polynomialCarrier sourceEndpointCarrier polynomialEndpointCarrier
    errorLedgerRel errorEndpointRel provenanceRel
  have continuousSourceCarrier : UnaryHistory continuousSource := continuousCarrier.left.left
  have polynomialCandidateCarrier : UnaryHistory polynomialCandidate := by
    cases polynomialCarrier
    exact unary_empty
  have errorLedgerCarrier : UnaryHistory errorLedger :=
    unary_cont_closed continuousSourceCarrier polynomialCandidateCarrier errorLedgerRel
  have errorEndpointCarrier : UnaryHistory errorEndpoint :=
    unary_cont_closed sourceEndpointCarrier polynomialEndpointCarrier errorEndpointRel
  constructor
  · exact errorLedgerCarrier
  · constructor
    · exact errorEndpointCarrier
    · constructor
      · exact errorLedgerRel
      · constructor
        · exact errorEndpointRel
        · exact provenanceRel

end BEDC.Derived.ApproximationUp
