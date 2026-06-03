import BEDC.Derived.FareySequenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceStreamApproximationTotality [AskSetup] [PackageSetup]
    {boundary adjacency mediant level tolerance stern density rationalSource streamWindow
      regRead approxRead realSeal transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier boundary adjacency mediant level tolerance stern density
        rationalSource streamWindow regRead approxRead realSeal transport replay provenance
        localName bundle pkg ->
      Cont streamWindow regRead approxRead ->
        Cont approxRead realSeal replay ->
          PkgSig bundle replay pkg ->
            UnaryHistory streamWindow ∧ UnaryHistory regRead ∧ UnaryHistory approxRead ∧
              UnaryHistory realSeal ∧ UnaryHistory replay ∧
                Cont streamWindow regRead approxRead ∧ Cont approxRead realSeal replay ∧
                  PkgSig bundle replay pkg := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier approximationRoute replayRoute replayPkg
  obtain ⟨_boundaryUnary, _adjacencyUnary, _mediantUnary, _levelUnary, _toleranceUnary,
    _sternUnary, _densityUnary, _rationalSourceUnary, streamUnary, regUnary,
    _approxCarrierUnary, realSealUnary, _transportUnary, _replayCarrierUnary,
    _provenanceUnary, _localNameUnary, _adjacencyEmpty, _sternEmpty, _mediantEmpty,
    _approxEmpty, _realSealEmpty, _provenancePkg⟩ := carrier
  have approxUnary : UnaryHistory approxRead :=
    unary_cont_closed streamUnary regUnary approximationRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed approxUnary realSealUnary replayRoute
  exact
    ⟨streamUnary, regUnary, approxUnary, realSealUnary, replayUnary, approximationRoute,
      replayRoute, replayPkg⟩

end BEDC.Derived.FareySequenceUp
