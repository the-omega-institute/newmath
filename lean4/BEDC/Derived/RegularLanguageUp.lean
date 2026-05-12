import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularLanguageUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularLanguageAutomatonPacket [AskSetup] [PackageSetup]
    (alphabet states start accept transition word run endpoint transport routes provenance :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory alphabet ∧ UnaryHistory states ∧ UnaryHistory start ∧ UnaryHistory accept ∧
    UnaryHistory transition ∧ UnaryHistory word ∧ UnaryHistory run ∧
      UnaryHistory endpoint ∧ UnaryHistory transport ∧ UnaryHistory routes ∧
        UnaryHistory provenance ∧ Cont start word run ∧ Cont run transition endpoint ∧
          Cont endpoint transport routes ∧ PkgSig bundle provenance pkg

theorem RegularLanguageAutomatonPacket_run_ledger_deterministic [AskSetup] [PackageSetup]
    {alphabet states start accept transition word run endpoint transport routes provenance run'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularLanguageAutomatonPacket alphabet states start accept transition word run endpoint
        transport routes provenance bundle pkg ->
      Cont start word run' -> Cont run' transition endpoint' ->
        hsame run run' ∧ hsame endpoint endpoint' := by
  intro packet runRow' endpointRow'
  obtain ⟨_alphabetUnary, _statesUnary, _startUnary, _acceptUnary, _transitionUnary,
    _wordUnary, _runUnary, _endpointUnary, _transportUnary, _routesUnary, _provenanceUnary,
    runRow, endpointRow, _routesRow, _pkgSig⟩ := packet
  have sameRun : hsame run run' :=
    cont_deterministic runRow runRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameRun (hsame_refl transition) endpointRow endpointRow'
  exact ⟨sameRun, sameEndpoint⟩

end BEDC.Derived.RegularLanguageUp
