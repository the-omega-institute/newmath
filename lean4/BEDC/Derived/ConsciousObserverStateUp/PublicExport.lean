import BEDC.Derived.ConsciousObserverStateUp

namespace BEDC.Derived.ConsciousObserverStateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ConsciousObserverStateCarrier_public_export [AskSetup] [PackageSetup]
    {observer state recognition ledger gap transport route provenance nameRow endpoint
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConsciousObserverStateCarrier observer state recognition ledger gap transport route provenance
        nameRow endpoint bundle pkg →
      Cont route provenance publicRead →
        PkgSig bundle publicRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ConsciousObserverStateCarrier observer state recognition ledger gap transport route
                  provenance nameRow endpoint bundle pkg ∧ hsame row publicRead)
              (fun row : BHist => UnaryHistory row ∧ Cont route provenance publicRead)
              (fun _row : BHist =>
                PkgSig bundle endpoint pkg ∧ PkgSig bundle publicRead pkg ∧
                  Cont observer route endpoint)
              hsame ∧
            UnaryHistory observer ∧ UnaryHistory state ∧ UnaryHistory recognition ∧
              UnaryHistory ledger ∧ UnaryHistory gap ∧ UnaryHistory publicRead ∧
                Cont observer route endpoint ∧ Cont state route endpoint ∧
                  Cont recognition ledger gap ∧ Cont route provenance publicRead ∧
                    PkgSig bundle endpoint pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier routeProvenancePublic publicPkg
  have carrierPacket :
      ConsciousObserverStateCarrier observer state recognition ledger gap transport route
        provenance nameRow endpoint bundle pkg :=
    carrier
  obtain ⟨observerUnary, stateUnary, recognitionUnary, ledgerUnary, gapUnary,
    _transportUnary, routeUnary, provenanceUnary, _nameUnary, _endpointUnary,
    observerRouteEndpoint, stateRouteEndpoint, recognitionLedgerGap,
    _transportProvenanceEndpoint, endpointPkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenancePublic
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ConsciousObserverStateCarrier observer state recognition ledger gap transport route
              provenance nameRow endpoint bundle pkg ∧ hsame row publicRead)
          (fun row : BHist => UnaryHistory row ∧ Cont route provenance publicRead)
          (fun _row : BHist =>
            PkgSig bundle endpoint pkg ∧ PkgSig bundle publicRead pkg ∧
              Cont observer route endpoint)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro publicRead (And.intro carrierPacket (hsame_refl publicRead))
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
      }
      pattern_sound := by
        intro row source
        exact And.intro (unary_transport publicUnary (hsame_symm source.right))
          routeProvenancePublic
      ledger_sound := by
        intro _row _source
        exact And.intro endpointPkg (And.intro publicPkg observerRouteEndpoint)
    }
  exact
    ⟨cert, observerUnary, stateUnary, recognitionUnary, ledgerUnary, gapUnary, publicUnary,
      observerRouteEndpoint, stateRouteEndpoint, recognitionLedgerGap, routeProvenancePublic,
      endpointPkg, publicPkg⟩

end BEDC.Derived.ConsciousObserverStateUp
