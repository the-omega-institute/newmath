import BEDC.Derived.ConsciousObserverStateUp

namespace BEDC.Derived.ConsciousObserverStateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ConsciousObserverStateCarrier_gap_locality_exhaustion [AskSetup] [PackageSetup]
    {observer state recognition ledger gap transport route provenance name endpoint gapRead
      handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConsciousObserverStateCarrier observer state recognition ledger gap transport route provenance
        name endpoint bundle pkg →
      hsame gapRead gap →
        Cont route provenance handoffRead →
          PkgSig bundle handoffRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  ConsciousObserverStateCarrier observer state recognition ledger gap transport
                    route provenance name endpoint bundle pkg ∧ hsame row gap)
                (fun row : BHist =>
                  hsame row gap ∧ UnaryHistory row ∧ Cont recognition ledger gap)
                (fun row : BHist =>
                  PkgSig bundle endpoint pkg ∧ PkgSig bundle handoffRead pkg ∧
                    hsame row gap ∧ Cont observer route endpoint ∧
                      Cont route provenance handoffRead)
                hsame ∧
              UnaryHistory gapRead ∧ UnaryHistory handoffRead ∧
                Cont recognition ledger gap ∧ Cont observer route endpoint ∧
                  Cont route provenance handoffRead ∧ PkgSig bundle endpoint pkg ∧
                    PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier gapReadSame handoffCont handoffPkg
  have carrierPacket :
      ConsciousObserverStateCarrier observer state recognition ledger gap transport route
        provenance name endpoint bundle pkg :=
    carrier
  obtain ⟨_observerUnary, _stateUnary, _recognitionUnary, _ledgerUnary, gapUnary,
    _transportUnary, routeUnary, provenanceUnary, _nameUnary, _endpointUnary,
    observerRouteEndpoint, _stateRouteEndpoint, recognitionLedgerGap,
    _transportProvenanceEndpoint, endpointPkg⟩ := carrier
  have gapReadUnary : UnaryHistory gapRead :=
    unary_transport gapUnary (hsame_symm gapReadSame)
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed routeUnary provenanceUnary handoffCont
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ConsciousObserverStateCarrier observer state recognition ledger gap transport route
              provenance name endpoint bundle pkg ∧ hsame row gap)
          (fun row : BHist =>
            hsame row gap ∧ UnaryHistory row ∧ Cont recognition ledger gap)
          (fun row : BHist =>
            PkgSig bundle endpoint pkg ∧ PkgSig bundle handoffRead pkg ∧
              hsame row gap ∧ Cont observer route endpoint ∧
                Cont route provenance handoffRead)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro gap ⟨carrierPacket, hsame_refl gap⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      have rowSameGap : hsame row gap := source.right
      exact
        ⟨rowSameGap, unary_transport gapUnary (hsame_symm rowSameGap),
          recognitionLedgerGap⟩
    · intro row source
      exact ⟨endpointPkg, handoffPkg, source.right, observerRouteEndpoint, handoffCont⟩
  exact
    ⟨cert, gapReadUnary, handoffUnary, recognitionLedgerGap, observerRouteEndpoint,
      handoffCont, endpointPkg, handoffPkg⟩

end BEDC.Derived.ConsciousObserverStateUp
