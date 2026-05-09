import BEDC.Derived.ContinuousMapUp
import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.ApproximationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ContinuousMapUp
open BEDC.Derived.PolynomialUp

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
