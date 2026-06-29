import BEDC.Derived.SubmartingaleUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SubmartingaleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubmartingaleCarrier_stopping_window_handoff [AskSetup] [PackageSetup]
    {omega random conditional filtration endpoints expectations comparison time transport replay
      provenance localName stopRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubmartingaleCarrier omega random conditional filtration endpoints expectations comparison time
        transport replay provenance localName bundle pkg →
      Cont time replay stopRead →
        Cont stopRead comparison handoffRead →
          PkgSig bundle handoffRead pkg →
            UnaryHistory stopRead ∧ UnaryHistory handoffRead ∧
              Cont time replay stopRead ∧ Cont stopRead comparison handoffRead ∧
                PkgSig bundle localName pkg ∧ PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier stopRoute handoffRoute handoffPkg
  obtain ⟨_omegaUnary, _randomUnary, _conditionalUnary, _filtrationUnary, _endpointsUnary,
    _expectationsUnary, comparisonUnary, timeUnary, _transportUnary, replayUnary,
    _provenanceUnary, _localNameUnary, localNamePkg⟩ := carrier
  have stopUnary : UnaryHistory stopRead :=
    unary_cont_closed timeUnary replayUnary stopRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed stopUnary comparisonUnary handoffRoute
  exact ⟨stopUnary, handoffUnary, stopRoute, handoffRoute, localNamePkg, handoffPkg⟩

end BEDC.Derived.SubmartingaleUp
