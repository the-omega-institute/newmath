import BEDC.Derived.ConsciousObserverStateUp

namespace BEDC.Derived.ConsciousObserverStateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ConsciousObserverStateCarrier_classifier_stability [AskSetup] [PackageSetup]
    {observer state recognition ledger gap transport route provenance nameRow endpoint
      otherEndpoint classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConsciousObserverStateCarrier observer state recognition ledger gap transport route provenance
        nameRow endpoint bundle pkg →
      hsame endpoint otherEndpoint →
        Cont endpoint otherEndpoint classifierRead →
          PkgSig bundle classifierRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  ConsciousObserverStateCarrier observer state recognition ledger gap transport route
                      provenance nameRow endpoint bundle pkg ∧
                    hsame row otherEndpoint)
                (fun row : BHist => hsame row otherEndpoint ∧ UnaryHistory row)
                (fun row : BHist =>
                  PkgSig bundle endpoint pkg ∧ hsame row otherEndpoint ∧
                    Cont endpoint otherEndpoint classifierRead)
                hsame ∧
              UnaryHistory classifierRead ∧
                Cont observer route endpoint ∧
                  Cont state route endpoint ∧
                    PkgSig bundle classifierRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier sameEndpoint endpointClassifier classifierPkg
  have carrierPacket :
      ConsciousObserverStateCarrier observer state recognition ledger gap transport route
        provenance nameRow endpoint bundle pkg :=
    carrier
  obtain ⟨_observerUnary, _stateUnary, _recognitionUnary, _ledgerUnary, _gapUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, endpointUnary,
    observerRouteEndpoint, stateRouteEndpoint, _recognitionLedgerGap,
    _transportProvenanceEndpoint, endpointPkg⟩ := carrier
  have otherEndpointUnary : UnaryHistory otherEndpoint :=
    unary_transport endpointUnary sameEndpoint
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed endpointUnary otherEndpointUnary endpointClassifier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ConsciousObserverStateCarrier observer state recognition ledger gap transport route
                provenance nameRow endpoint bundle pkg ∧
              hsame row otherEndpoint)
          (fun row : BHist => hsame row otherEndpoint ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle endpoint pkg ∧ hsame row otherEndpoint ∧
              Cont endpoint otherEndpoint classifierRead)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro otherEndpoint ⟨carrierPacket, hsame_refl otherEndpoint⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      have rowSameOther : hsame row otherEndpoint := source.right
      exact
        ⟨rowSameOther,
          unary_transport otherEndpointUnary (hsame_symm rowSameOther)⟩
    · intro row source
      exact ⟨endpointPkg, source.right, endpointClassifier⟩
  exact
    ⟨cert, classifierUnary, observerRouteEndpoint, stateRouteEndpoint, classifierPkg⟩

end BEDC.Derived.ConsciousObserverStateUp
