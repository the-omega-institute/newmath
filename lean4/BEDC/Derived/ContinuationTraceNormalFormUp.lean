import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ContinuationTraceNormalFormUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.ContinuationTraceNormalFormUp
