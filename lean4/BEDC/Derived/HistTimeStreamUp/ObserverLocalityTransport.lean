import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_observer_locality_transport [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name observerRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg ->
      Cont provenance name observerRead ->
        Cont observerRead replay endpoint ->
          PkgSig bundle endpoint pkg ->
            UnaryHistory observerRead ∧ UnaryHistory endpoint ∧
              Cont provenance name observerRead ∧ Cont observerRead replay endpoint ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg Cont
  intro carrier provenanceNameObserver observerReplayEndpoint endpointPkg
  obtain ⟨_sourceUnary, _scheduleUnary, _startUnary, replayUnary, _transportUnary,
    provenanceUnary, nameUnary, _scheduleStartReplay, _sourceReplayProvenance,
    _provenanceReplay, provenancePkg, _namePkg⟩ := carrier
  have observerUnary : UnaryHistory observerRead :=
    unary_cont_closed provenanceUnary nameUnary provenanceNameObserver
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed observerUnary replayUnary observerReplayEndpoint
  exact
    ⟨observerUnary, endpointUnary, provenanceNameObserver, observerReplayEndpoint,
      provenancePkg, endpointPkg⟩

end BEDC.Derived.HistTimeStreamUp
