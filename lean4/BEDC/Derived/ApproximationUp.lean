import BEDC.Derived.ContinuousMapUp
import BEDC.Derived.PolynomialUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem ApproximationCarrierPacket_polynomial_consumer_window [AskSetup] [PackageSetup]
    {continuousSource continuousMap continuousTarget modulus continuousCert continuousDistance
      polynomialCandidate errorEndpoint errorLedger transportLedger provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuousMapCarrier continuousSource continuousMap continuousTarget modulus continuousCert
        continuousDistance ->
      PolynomialSingletonCarrier polynomialCandidate ->
        UnaryHistory transportLedger ->
          Cont continuousTarget polynomialCandidate errorEndpoint ->
            Cont errorEndpoint transportLedger errorLedger ->
              PkgSig bundle provenance pkg ->
                SemanticNameCert (fun row : BHist => hsame row errorLedger)
                  (fun row : BHist => hsame row errorLedger)
                  (fun row : BHist => hsame row errorLedger) hsame ∧
                  PolynomialSingletonCarrier polynomialCandidate ∧ UnaryHistory errorEndpoint ∧
                    UnaryHistory errorLedger ∧
                      hsame errorEndpoint (append continuousTarget polynomialCandidate) ∧
                        Cont errorEndpoint transportLedger errorLedger ∧
                          PkgSig bundle provenance pkg := by
  intro continuousCarrier polynomialCarrier transportUnary endpointRow ledgerRow provenancePkg
  have rows :=
    ApproximationCarrierPacket_obligation_surface continuousCarrier polynomialCarrier transportUnary
      endpointRow ledgerRow provenancePkg
  have cert :
      SemanticNameCert (fun row : BHist => hsame row errorLedger)
        (fun row : BHist => hsame row errorLedger)
        (fun row : BHist => hsame row errorLedger) hsame := {
    core := {
      carrier_inhabited := Exists.intro errorLedger (hsame_refl errorLedger)
      equiv_refl := by
        intro row _carrier
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows carrierRow
        exact hsame_trans (hsame_symm sameRows) carrierRow
    }
    pattern_sound := by
      intro _row carrier
      exact carrier
    ledger_sound := by
      intro _row carrier
      exact carrier
  }
  exact And.intro cert
    (And.intro rows.right.left
      (And.intro rows.right.right.left
        (And.intro rows.right.right.right.left
          (And.intro rows.right.right.right.right.left
            (And.intro rows.right.right.right.right.right.left
              rows.right.right.right.right.right.right)))))

theorem ApproximationCarrierPacket_error_ledger_exactness [AskSetup] [PackageSetup]
    {continuousSource continuousMap continuousTarget modulus continuousCert continuousDistance
      polynomialCandidate errorEndpoint errorLedger transportLedger provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuousMapCarrier continuousSource continuousMap continuousTarget modulus continuousCert
        continuousDistance ->
      PolynomialSingletonCarrier polynomialCandidate ->
        UnaryHistory transportLedger ->
          Cont continuousTarget polynomialCandidate errorEndpoint ->
            Cont errorEndpoint transportLedger errorLedger ->
              PkgSig bundle provenance pkg ->
                UnaryHistory errorEndpoint ∧ UnaryHistory errorLedger ∧
                  hsame errorEndpoint (append continuousTarget polynomialCandidate) ∧
                    hsame errorLedger (append errorEndpoint transportLedger) ∧
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
  exact And.intro endpointUnary
    (And.intro ledgerUnary
      (And.intro endpointRow
        (And.intro ledgerRow provenancePkg)))

end BEDC.Derived.ApproximationUp
