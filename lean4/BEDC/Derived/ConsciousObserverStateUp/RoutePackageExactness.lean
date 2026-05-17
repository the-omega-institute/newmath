import BEDC.Derived.ConsciousObserverStateUp

namespace BEDC.Derived.ConsciousObserverStateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ConsciousObserverStateCarrier_route_package_exactness [AskSetup] [PackageSetup]
    {observer state recognition ledger gap transport route provenance nameRow endpoint scopeRead
      packageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConsciousObserverStateCarrier observer state recognition ledger gap transport route provenance
        nameRow endpoint bundle pkg →
      Cont route provenance scopeRead →
        Cont scopeRead gap packageRead →
          PkgSig bundle packageRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  ConsciousObserverStateCarrier observer state recognition ledger gap transport
                    route provenance nameRow endpoint bundle pkg ∧ hsame row packageRead)
                (fun row : BHist => UnaryHistory row ∧ hsame row packageRead)
                (fun _row : BHist =>
                  Cont route provenance scopeRead ∧ Cont scopeRead gap packageRead ∧
                    PkgSig bundle endpoint pkg ∧ PkgSig bundle packageRead pkg)
                hsame ∧
              UnaryHistory observer ∧ UnaryHistory state ∧ UnaryHistory recognition ∧
              UnaryHistory ledger ∧ UnaryHistory gap ∧ UnaryHistory scopeRead ∧
              UnaryHistory packageRead ∧ Cont observer route endpoint ∧
              Cont recognition ledger gap ∧ Cont route provenance scopeRead ∧
              Cont scopeRead gap packageRead ∧ PkgSig bundle endpoint pkg ∧
              PkgSig bundle packageRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier routeProvenanceScope scopeGapPackage packagePkg
  have carrierPacket :
      ConsciousObserverStateCarrier observer state recognition ledger gap transport route
        provenance nameRow endpoint bundle pkg :=
    carrier
  obtain ⟨observerUnary, stateUnary, recognitionUnary, ledgerUnary, gapUnary, _transportUnary,
    routeUnary, provenanceUnary, _nameUnary, _endpointUnary, observerRouteEndpoint,
    _stateRouteEndpoint, recognitionLedgerGap, _transportProvenanceEndpoint, endpointPkg⟩ :=
    carrier
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceScope
  have packageUnary : UnaryHistory packageRead :=
    unary_cont_closed scopeUnary gapUnary scopeGapPackage
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ConsciousObserverStateCarrier observer state recognition ledger gap transport route
              provenance nameRow endpoint bundle pkg ∧ hsame row packageRead)
          (fun row : BHist => UnaryHistory row ∧ hsame row packageRead)
          (fun _row : BHist =>
            Cont route provenance scopeRead ∧ Cont scopeRead gap packageRead ∧
              PkgSig bundle endpoint pkg ∧ PkgSig bundle packageRead pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro packageRead ⟨carrierPacket, hsame_refl packageRead⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      exact ⟨unary_transport packageUnary (hsame_symm source.right), source.right⟩
    · intro _row _source
      exact ⟨routeProvenanceScope, scopeGapPackage, endpointPkg, packagePkg⟩
  exact
    ⟨cert, observerUnary, stateUnary, recognitionUnary, ledgerUnary, gapUnary, scopeUnary,
      packageUnary, observerRouteEndpoint, recognitionLedgerGap, routeProvenanceScope,
      scopeGapPackage, endpointPkg, packagePkg⟩

end BEDC.Derived.ConsciousObserverStateUp
