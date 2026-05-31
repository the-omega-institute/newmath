import BEDC.Derived.CauchySequenceBoundedUp.TasteGate
import BEDC.Derived.RealSequenceLimitUp

namespace BEDC.Derived.RealSequenceLimitUp.BoundedSourceHandoff

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.CauchySequenceBoundedUp

theorem RealSequenceLimitBoundedSourceHandoff [AskSetup] [PackageSetup]
    {sequence limit window dyadic classifier transport replay provenance name boundedModulus
      boundedTolerance boundedReadback boundedSeal boundedBound boundedTransport boundedRoute
      boundedProvenance boundedName boundedExit realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RealSequenceLimitUp sequence limit window dyadic classifier transport replay
        provenance name bundle pkg ->
      CauchySequenceBoundedCarrier sequence boundedModulus boundedTolerance boundedReadback
        boundedSeal boundedBound boundedTransport boundedRoute boundedProvenance boundedName
        bundle pkg ->
        Cont boundedBound window boundedExit ->
          Cont boundedExit classifier realSeal ->
            PkgSig bundle realSeal pkg ->
              UnaryHistory sequence ∧ UnaryHistory boundedBound ∧ UnaryHistory window ∧
                UnaryHistory classifier ∧ UnaryHistory boundedExit ∧ UnaryHistory realSeal ∧
                  Cont boundedBound window boundedExit ∧ Cont boundedExit classifier realSeal ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro limitCarrier boundedCarrier boundedExitRoute realSealRoute realSealPkg
  rcases limitCarrier with
    ⟨_sequenceUnary, _limitUnary, windowUnary, _dyadicUnary, classifierUnary,
      _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _sequenceRoute,
      _classifierRoute, _transportSame, _replaySame, _provenancePkg, namePkg⟩
  rcases boundedCarrier with
    ⟨sequenceUnary, _boundedModulusUnary, _boundedToleranceUnary, boundedBoundUnary,
      _boundedRouteUnary, _boundedProvenanceUnary, _boundedToleranceRoute,
      _boundedReadbackRoute, _boundedSealRoute, _boundedNameRoute, _boundedNamePkg⟩
  have boundedExitUnary : UnaryHistory boundedExit :=
    unary_cont_closed boundedBoundUnary windowUnary boundedExitRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed boundedExitUnary classifierUnary realSealRoute
  exact
    ⟨sequenceUnary, boundedBoundUnary, windowUnary, classifierUnary, boundedExitUnary,
      realSealUnary, boundedExitRoute, realSealRoute, namePkg, realSealPkg⟩

end BEDC.Derived.RealSequenceLimitUp.BoundedSourceHandoff
