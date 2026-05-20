import BEDC.Derived.RegSeqRatUp
import BEDC.Derived.StreamNameUp

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RegSeqRatUp

theorem StreamNameCommonRefinementTerminalRealSeal [AskSetup] [PackageSetup]
    {s t : BHist -> BHist} {window : ProbeBundle BHist}
    {packageBundle : ProbeBundle ProbeName}
    {schedule index endpoint radius regularity provenance readback realSeal terminal : BHist}
    {pkg : Pkg} :
    RatStreamNameCarrier s ->
      RatStreamNameCarrier t ->
        RatStreamNameFiniteWindowClassifier s t window ->
          RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance readback
              packageBundle pkg ->
            UnaryHistory realSeal ->
              Cont readback realSeal terminal ->
                PkgSig packageBundle terminal pkg ->
                UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory terminal ∧
                  RatStreamNameFiniteWindowClassifier s t window ∧
                    Cont readback realSeal terminal ∧ PkgSig packageBundle readback pkg ∧
                      PkgSig packageBundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig UnaryHistory
  intro _carrierS _carrierT windowClassifier regseqCarrier realSealUnary sealRoute terminalPkg
  obtain
    ⟨_scheduleUnary, _indexUnary, _endpointUnary, _radiusUnary, _regularityUnary,
      _provenanceUnary, readbackUnary, _scheduleRoute, _regularityRoute, _readbackRoute,
      readbackPkg⟩ := regseqCarrier
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed readbackUnary realSealUnary sealRoute
  exact
    ⟨readbackUnary, realSealUnary, terminalUnary, windowClassifier, sealRoute, readbackPkg,
      terminalPkg⟩

end BEDC.Derived.StreamNameUp
