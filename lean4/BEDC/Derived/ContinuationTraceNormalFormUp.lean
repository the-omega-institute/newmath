import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ContinuationTraceNormalFormUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ContinuationTraceNormalFormCarrier [AskSetup] [PackageSetup]
    (source trace terminal terminalRead normal transport route provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory trace ∧ UnaryHistory terminal ∧
    UnaryHistory terminalRead ∧ UnaryHistory normal ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory cert ∧
        Cont source trace terminal ∧ Cont terminal terminalRead route ∧
          PkgSig bundle provenance pkg

theorem ContinuationTraceNormalFormCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source trace terminal terminalRead normal transport route provenance cert replay endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationTraceNormalFormCarrier source trace terminal terminalRead normal transport route
        provenance cert bundle pkg →
      Cont trace route replay →
        Cont replay normal endpoint →
          PkgSig bundle endpoint pkg →
            UnaryHistory replay ∧ UnaryHistory endpoint ∧ Cont trace route replay ∧
              Cont replay normal endpoint ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro carrier traceRouteReplay replayNormalEndpoint endpointPkg
  obtain ⟨_sourceUnary, traceUnary, _terminalUnary, _terminalReadUnary, normalUnary,
    _transportUnary, routeUnary, _provenanceUnary, _certUnary, _sourceTraceTerminal,
    _terminalReadRoute, provenancePkg⟩ := carrier
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed traceUnary routeUnary traceRouteReplay
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed replayUnary normalUnary replayNormalEndpoint
  exact
    ⟨replayUnary, endpointUnary, traceRouteReplay, replayNormalEndpoint, provenancePkg,
      endpointPkg⟩

theorem ContinuationTraceNormalFormUp_StdBridge [AskSetup] [PackageSetup]
    {source trace terminal terminalRead normal transport route provenance cert replay endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationTraceNormalFormCarrier source trace terminal terminalRead normal transport route
        provenance cert bundle pkg ->
      Cont trace route replay ->
        Cont replay normal endpoint ->
          PkgSig bundle endpoint pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row endpoint ∧ UnaryHistory row ∧
                PkgSig bundle row pkg)
              (fun row : BHist => Cont trace route replay ∧ Cont replay normal row)
              (fun row : BHist => PkgSig bundle row pkg ∧ Cont replay normal row)
              (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist SemanticNameCert Cont ProbeBundle Pkg hsame
  intro carrier traceRouteReplay replayNormalEndpoint endpointPkg
  obtain ⟨_sourceUnary, traceUnary, _terminalUnary, _terminalReadUnary, normalUnary,
    _transportUnary, routeUnary, _provenanceUnary, _certUnary, _sourceTraceTerminal,
    _terminalReadRoute, _provenancePkg⟩ := carrier
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed traceUnary routeUnary traceRouteReplay
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed replayUnary normalUnary replayNormalEndpoint
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint ⟨hsame_refl endpoint, endpointUnary, endpointPkg⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        cases same
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨traceRouteReplay,
          cont_result_hsame_transport replayNormalEndpoint (hsame_symm sourceRow.left)⟩
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right.right,
          cont_result_hsame_transport replayNormalEndpoint (hsame_symm sourceRow.left)⟩
  }

theorem ContinuationTraceNormalFormCarrier_source_normalization_obligation [AskSetup]
    [PackageSetup]
    {source trace terminal terminalRead normal transport route provenance cert replay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationTraceNormalFormCarrier source trace terminal terminalRead normal transport route
        provenance cert bundle pkg →
      Cont trace route replay →
        PkgSig bundle replay pkg →
          UnaryHistory source ∧ UnaryHistory trace ∧ UnaryHistory route ∧ UnaryHistory cert ∧
            UnaryHistory replay ∧ Cont source trace terminal ∧ Cont trace route replay ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle replay pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro carrier traceRouteReplay replayPkg
  obtain ⟨sourceUnary, traceUnary, _terminalUnary, _terminalReadUnary, _normalUnary,
    _transportUnary, routeUnary, _provenanceUnary, certUnary, sourceTraceTerminal,
    _terminalReadRoute, provenancePkg⟩ := carrier
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed traceUnary routeUnary traceRouteReplay
  exact
    ⟨sourceUnary, traceUnary, routeUnary, certUnary, replayUnary, sourceTraceTerminal,
      traceRouteReplay, provenancePkg, replayPkg⟩

end BEDC.Derived.ContinuationTraceNormalFormUp
