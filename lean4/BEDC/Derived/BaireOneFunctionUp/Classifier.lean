import BEDC.Derived.BaireOneFunctionUp

namespace BEDC.Derived.BaireOneFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BaireOneFunctionClassifier
    (X F S Q R L H C P N X' F' S' Q' R' L' H' C' P' N' : BHist) : Prop :=
  hsame X X' ∧ hsame F F' ∧ hsame S S' ∧ hsame Q Q' ∧ hsame R R' ∧
    hsame L L' ∧ hsame H H' ∧ hsame C C' ∧ hsame P P' ∧ hsame N N'

theorem BaireOneFunctionClassifier_component_transport [AskSetup] [PackageSetup]
    {X F S Q R L H C P N X' F' S' Q' R' L' H' C' P' N' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg →
      BaireOneFunctionCarrier X' F' S' Q' R' L' H' C' P' N' bundle pkg →
        BaireOneFunctionClassifier X F S Q R L H C P N X' F' S' Q' R' L' H' C' P' N' →
          UnaryHistory X' ∧ UnaryHistory F' ∧ UnaryHistory S' ∧ UnaryHistory Q' ∧
            UnaryHistory R' ∧ UnaryHistory L' ∧ UnaryHistory H' ∧ UnaryHistory C' ∧
              PkgSig bundle P' pkg ∧ PkgSig bundle N' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame UnaryHistory PkgSig
  intro carrier _targetCarrier classified
  obtain ⟨xUnary, fUnary, sUnary, qUnary, rUnary, lUnary, hUnary, cUnary,
    _pUnary, _nUnary, _sourceApproxSchedule, _scheduleReadbackReal,
    _realHandoffTransport, _transportContinuationProvenance, _provenancePkg,
    _namePkg⟩ := carrier
  obtain ⟨_targetXUnary, _targetFUnary, _targetSUnary, _targetQUnary, _targetRUnary,
    _targetLUnary, _targetHUnary, _targetCUnary, _targetPUnary, _targetNUnary,
    _targetSourceApproxSchedule, _targetScheduleReadbackReal, _targetRealHandoffTransport,
    _targetTransportContinuationProvenance, targetProvenancePkg, targetNamePkg⟩ :=
    _targetCarrier
  obtain ⟨sameX, sameF, sameS, sameQ, sameR, sameL, sameH, sameC, _sameP, _sameN⟩ :=
    classified
  exact
    ⟨unary_transport xUnary sameX, unary_transport fUnary sameF,
      unary_transport sUnary sameS, unary_transport qUnary sameQ,
      unary_transport rUnary sameR, unary_transport lUnary sameL,
      unary_transport hUnary sameH, unary_transport cUnary sameC,
      targetProvenancePkg, targetNamePkg⟩

end BEDC.Derived.BaireOneFunctionUp
