import BEDC.Derived.HausdorffCompletionUp

namespace BEDC.Derived.HausdorffCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HausdorffCompletionCarrier_standard_bridge_source_packet [AskSetup] [PackageSetup]
    {source entourage separated handoff transport route provenance bridgeSource : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffCompletionCarrier source entourage separated handoff transport route provenance
        bundle pkg ->
      Cont source handoff bridgeSource ->
        PkgSig bundle bridgeSource pkg ->
          UnaryHistory source ∧ UnaryHistory entourage ∧ UnaryHistory separated ∧
            UnaryHistory handoff ∧ UnaryHistory transport ∧ UnaryHistory route ∧
              UnaryHistory provenance ∧ UnaryHistory bridgeSource ∧
                Cont source entourage transport ∧ Cont separated handoff route ∧
                  Cont transport route provenance ∧ Cont source handoff bridgeSource ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle bridgeSource pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg
  intro carrier sourceHandoffBridgeSource bridgeSourcePkg
  obtain ⟨sourceUnary, entourageUnary, separatedUnary, handoffUnary, transportUnary,
    routeUnary, provenanceUnary, sourceEntourageTransport, separatedHandoffRoute,
    transportRouteProvenance, provenancePkg⟩ := carrier
  have bridgeSourceUnary : UnaryHistory bridgeSource :=
    unary_cont_closed sourceUnary handoffUnary sourceHandoffBridgeSource
  exact
    ⟨sourceUnary, entourageUnary, separatedUnary, handoffUnary, transportUnary, routeUnary,
      provenanceUnary, bridgeSourceUnary, sourceEntourageTransport, separatedHandoffRoute,
      transportRouteProvenance, sourceHandoffBridgeSource, provenancePkg, bridgeSourcePkg⟩

theorem HausdorffCompletionUp_StdBridge [AskSetup] [PackageSetup]
    {source entourage separated handoff transport route provenance bridgeSource standardRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffCompletionCarrier source entourage separated handoff transport route provenance
        bundle pkg →
      Cont source handoff bridgeSource →
        Cont bridgeSource provenance standardRead →
          PkgSig bundle bridgeSource pkg →
            PkgSig bundle standardRead pkg →
              SemanticNameCert
                (fun row : BHist =>
                  hsame row standardRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                (fun row : BHist =>
                  Cont bridgeSource provenance row ∧ Cont source handoff bridgeSource ∧
                    HausdorffCompletionCarrier source entourage separated handoff transport route
                      provenance bundle pkg)
                (fun row : BHist =>
                  PkgSig bundle row pkg ∧ Cont bridgeSource provenance standardRead)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier sourceHandoffBridgeSource bridgeSourceProvenanceStandardRead _bridgeSourcePkg
    standardReadPkg
  have acceptedCarrier :
      HausdorffCompletionCarrier source entourage separated handoff transport route provenance
        bundle pkg :=
    carrier
  obtain ⟨sourceUnary, _entourageUnary, _separatedUnary, handoffUnary, _transportUnary,
    _routeUnary, provenanceUnary, _sourceEntourageTransport, _separatedHandoffRoute,
    _transportRouteProvenance, _provenancePkg⟩ := carrier
  have bridgeSourceUnary : UnaryHistory bridgeSource :=
    unary_cont_closed sourceUnary handoffUnary sourceHandoffBridgeSource
  have standardReadUnary : UnaryHistory standardRead :=
    unary_cont_closed bridgeSourceUnary provenanceUnary bridgeSourceProvenanceStandardRead
  refine
    { core :=
        { carrier_inhabited :=
            ⟨standardRead, hsame_refl standardRead, standardReadUnary, standardReadPkg⟩
          equiv_refl := ?_
          equiv_symm := ?_
          equiv_trans := ?_
          carrier_respects_equiv := ?_ }
      pattern_sound := ?_
      ledger_sound := ?_ }
  · intro row _source
    exact hsame_refl row
  · intro _row _row' sameRows
    exact hsame_symm sameRows
  · intro _row _row' _row'' sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro _row _row' sameRows sourceRow
    cases sameRows
    exact sourceRow
  · intro _row sourceRow
    exact
      ⟨cont_result_hsame_transport bridgeSourceProvenanceStandardRead
        (hsame_symm sourceRow.left),
      sourceHandoffBridgeSource,
      acceptedCarrier⟩
  · intro _row sourceRow
    exact ⟨sourceRow.right.right, bridgeSourceProvenanceStandardRead⟩

end BEDC.Derived.HausdorffCompletionUp
