import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_diagonal_budget_readback_compatibility
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      epsilon diagModulus diagWindow diagLedger diagKernel diagSeal diagonalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      hsame epsilon window ->
        UnaryHistory epsilon ->
          Cont epsilon modulus diagModulus ->
            Cont diagModulus window diagWindow ->
              Cont diagWindow ledger diagLedger ->
                Cont diagLedger realSeal diagKernel ->
                  Cont diagKernel endpoint diagSeal ->
                    Cont diagSeal provenance diagonalRead ->
                      PkgSig bundle diagonalRead pkg ->
                        UnaryHistory epsilon ∧ UnaryHistory diagModulus ∧
                          UnaryHistory diagWindow ∧ UnaryHistory diagLedger ∧
                            UnaryHistory diagKernel ∧ UnaryHistory diagSeal ∧
                              UnaryHistory diagonalRead ∧ hsame diagModulus tolerance ∧
                                Cont epsilon modulus diagModulus ∧
                                  Cont diagModulus window diagWindow ∧
                                    Cont diagWindow ledger diagLedger ∧
                                      Cont diagLedger realSeal diagKernel ∧
                                        Cont diagKernel endpoint diagSeal ∧
                                          Cont diagSeal provenance diagonalRead ∧
                                            PkgSig bundle endpoint pkg ∧
                                              PkgSig bundle diagonalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame UnaryHistory Cont PkgSig
  intro carrier sameEpsilonWindow epsilonUnary epsilonModulusDiagModulus
    diagModulusWindowDiagWindow diagWindowLedgerDiagLedger diagLedgerRealSealDiagKernel
    diagKernelEndpointDiagSeal diagSealProvenanceDiagonalRead diagonalPkg
  obtain ⟨_windowUnary, modulusUnary, _toleranceUnary, ledgerUnary, _regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, provenanceUnary, _localCertUnary,
    endpointUnary, windowModulusTolerance, _toleranceLedgerRegseq, _regseqRealSealTransport,
    _transportLocalCertRoute, _routeProvenanceEndpoint, endpointPkg⟩ := carrier
  have diagModulusUnary : UnaryHistory diagModulus :=
    unary_cont_closed epsilonUnary modulusUnary epsilonModulusDiagModulus
  have diagWindowUnary : UnaryHistory diagWindow :=
    unary_cont_closed diagModulusUnary (unary_transport epsilonUnary sameEpsilonWindow)
      diagModulusWindowDiagWindow
  have diagLedgerUnary : UnaryHistory diagLedger :=
    unary_cont_closed diagWindowUnary ledgerUnary diagWindowLedgerDiagLedger
  have diagKernelUnary : UnaryHistory diagKernel :=
    unary_cont_closed diagLedgerUnary realSealUnary diagLedgerRealSealDiagKernel
  have diagSealUnary : UnaryHistory diagSeal :=
    unary_cont_closed diagKernelUnary endpointUnary diagKernelEndpointDiagSeal
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed diagSealUnary provenanceUnary diagSealProvenanceDiagonalRead
  have sameDiagModulusTolerance : hsame diagModulus tolerance :=
    cont_respects_hsame sameEpsilonWindow (hsame_refl modulus) epsilonModulusDiagModulus
      windowModulusTolerance
  exact
    ⟨epsilonUnary, diagModulusUnary, diagWindowUnary, diagLedgerUnary, diagKernelUnary,
      diagSealUnary, diagonalReadUnary, sameDiagModulusTolerance, epsilonModulusDiagModulus,
      diagModulusWindowDiagWindow, diagWindowLedgerDiagLedger, diagLedgerRealSealDiagKernel,
      diagKernelEndpointDiagSeal, diagSealProvenanceDiagonalRead, endpointPkg, diagonalPkg⟩

end BEDC.Derived.CauchyCriterionUp
