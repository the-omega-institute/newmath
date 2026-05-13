import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteCauchyApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteCauchyApproximationCarrier [AskSetup] [PackageSetup]
    (source precision threshold window dyadic error handoff sameRows routes provenance
      localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory precision ∧ UnaryHistory threshold ∧
    UnaryHistory window ∧ UnaryHistory dyadic ∧ UnaryHistory error ∧
      UnaryHistory sameRows ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory localCert ∧ Cont source precision threshold ∧
          Cont threshold window dyadic ∧ Cont dyadic error handoff ∧
            Cont sameRows routes provenance ∧ Cont handoff localCert provenance ∧
              PkgSig bundle provenance pkg

theorem FiniteCauchyApproximationCarrier_window_soundness [AskSetup] [PackageSetup]
    {source precision threshold window dyadic error handoff sameRows routes provenance
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteCauchyApproximationCarrier source precision threshold window dyadic error handoff
        sameRows routes provenance localCert bundle pkg ->
      UnaryHistory window ∧ UnaryHistory dyadic ∧ UnaryHistory error ∧
        Cont threshold window dyadic ∧ Cont dyadic error handoff ∧
          PkgSig bundle provenance pkg := by
  intro carrier
  obtain ⟨_sourceUnary, _precisionUnary, _thresholdUnary, windowUnary, dyadicUnary,
    errorUnary, _sameRowsUnary, _routesUnary, _provenanceUnary, _localCertUnary,
    _sourcePrecisionThreshold, thresholdWindowDyadic, dyadicErrorHandoff,
    _sameRoutesProvenance, _handoffLocalProvenance, provenancePkg⟩ := carrier
  exact
    ⟨windowUnary, dyadicUnary, errorUnary, thresholdWindowDyadic, dyadicErrorHandoff,
      provenancePkg⟩

theorem FiniteCauchyApproximationCarrier_real_handoff [AskSetup] [PackageSetup]
    {source precision threshold window dyadic error handoff sameRows routes provenance
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteCauchyApproximationCarrier source precision threshold window dyadic error handoff
        sameRows routes provenance localCert bundle pkg ->
      UnaryHistory handoff ∧ Cont source precision threshold ∧ Cont threshold window dyadic ∧
        Cont dyadic error handoff ∧ Cont handoff localCert provenance ∧
          PkgSig bundle provenance pkg := by
  intro carrier
  obtain ⟨_sourceUnary, _precisionUnary, _thresholdUnary, _windowUnary, dyadicUnary,
    errorUnary, _sameRowsUnary, _routesUnary, _provenanceUnary, _localCertUnary,
    sourcePrecisionThreshold, thresholdWindowDyadic, dyadicErrorHandoff,
    _sameRoutesProvenance, handoffLocalProvenance, provenancePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed dyadicUnary errorUnary dyadicErrorHandoff
  exact
    ⟨handoffUnary, sourcePrecisionThreshold, thresholdWindowDyadic, dyadicErrorHandoff,
      handoffLocalProvenance, provenancePkg⟩

theorem FiniteCauchyApproximationCarrier_refinement_stability [AskSetup] [PackageSetup]
    {source precision threshold window dyadic error handoff sameRows routes provenance localCert
      source' precision' threshold' window' dyadic' error' handoff' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteCauchyApproximationCarrier source precision threshold window dyadic error handoff
        sameRows routes provenance localCert bundle pkg ->
      hsame source source' ->
        hsame precision precision' ->
          hsame threshold threshold' ->
            hsame window window' ->
              hsame dyadic dyadic' ->
                hsame error error' ->
                  Cont source' precision' threshold' ->
                    Cont threshold' window' dyadic' ->
                      Cont dyadic' error' handoff' ->
                        UnaryHistory dyadic' ∧ UnaryHistory error' ∧
                          UnaryHistory handoff' ∧ hsame handoff handoff' ∧
                            Cont threshold' window' dyadic' ∧
                              Cont dyadic' error' handoff' ∧
                                PkgSig bundle provenance pkg := by
  intro carrier sourceSame precisionSame thresholdSame windowSame dyadicSame errorSame
    _sourcePrecisionThreshold' thresholdWindowDyadic' dyadicErrorHandoff'
  obtain ⟨_sourceUnary, _precisionUnary, _thresholdUnary, _windowUnary, dyadicUnary,
    errorUnary, _sameRowsUnary, _routesUnary, _provenanceUnary, _localCertUnary,
    _sourcePrecisionThreshold, thresholdWindowDyadic, dyadicErrorHandoff,
    _sameRoutesProvenance, _handoffLocalProvenance, provenancePkg⟩ := carrier
  have dyadicUnary' : UnaryHistory dyadic' :=
    unary_transport dyadicUnary dyadicSame
  have errorUnary' : UnaryHistory error' :=
    unary_transport errorUnary errorSame
  have handoffUnary' : UnaryHistory handoff' :=
    unary_cont_closed dyadicUnary' errorUnary' dyadicErrorHandoff'
  have handoffSame : hsame handoff handoff' :=
    cont_respects_hsame dyadicSame errorSame dyadicErrorHandoff dyadicErrorHandoff'
  exact
    ⟨dyadicUnary', errorUnary', handoffUnary', handoffSame, thresholdWindowDyadic',
      dyadicErrorHandoff', provenancePkg⟩

end BEDC.Derived.FiniteCauchyApproximationUp
