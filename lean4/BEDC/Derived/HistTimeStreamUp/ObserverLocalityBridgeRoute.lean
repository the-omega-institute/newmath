import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamObserverLocalityBridgeRoute [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name observation localityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg →
      Cont source replay observation →
        Cont observation transport localityRead →
          PkgSig bundle observation pkg →
            PkgSig bundle localityRead pkg →
              UnaryHistory observation ∧ UnaryHistory localityRead ∧
                Cont source replay observation ∧ Cont observation transport localityRead ∧
                  hsame provenance replay ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle observation pkg ∧ PkgSig bundle localityRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame PkgSig ProbeBundle UnaryHistory
  intro carrier sourceReplayObservation observationTransportLocality observationPkg localityPkg
  obtain ⟨sourceUnary, _scheduleUnary, _startUnary, replayUnary, transportUnary,
    _provenanceUnary, _nameUnary, _scheduleStartReplay, _sourceReplayProvenance,
    provenanceReplay, provenancePkg, _namePkg⟩ := carrier
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed sourceUnary replayUnary sourceReplayObservation
  have localityUnary : UnaryHistory localityRead :=
    unary_cont_closed observationUnary transportUnary observationTransportLocality
  exact
    ⟨observationUnary, localityUnary, sourceReplayObservation, observationTransportLocality,
      provenanceReplay, provenancePkg, observationPkg, localityPkg⟩

end BEDC.Derived.HistTimeStreamUp
