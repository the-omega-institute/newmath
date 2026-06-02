import BEDC.Derived.FareySequenceUp.TasteGate

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequence_classifier_transport [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N transportedRoute transportedName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont H C transportedRoute ->
        Cont transportedRoute N transportedName ->
          PkgSig bundle transportedName pkg ->
            UnaryHistory B ∧ UnaryHistory A ∧ UnaryHistory M ∧ UnaryHistory L ∧
              UnaryHistory T ∧ UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory Q ∧
                UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory G ∧ UnaryHistory E ∧
                  UnaryHistory transportedRoute ∧ UnaryHistory transportedName ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle transportedName pkg := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle PkgSig
  intro carrier transportRoute nameRoute transportedPkg
  obtain ⟨bUnary, aUnary, mUnary, lUnary, tUnary, sUnary, dUnary, qUnary, wUnary,
    rUnary, gUnary, eUnary, hUnary, cUnary, _pUnary, nUnary, _aEmpty, _sEmpty,
    _mEmpty, _gEmpty, _eEmpty, provenancePkg⟩ := carrier
  have transportedRouteUnary : UnaryHistory transportedRoute :=
    unary_cont_closed hUnary cUnary transportRoute
  have transportedNameUnary : UnaryHistory transportedName :=
    unary_cont_closed transportedRouteUnary nUnary nameRoute
  exact
    ⟨bUnary, aUnary, mUnary, lUnary, tUnary, sUnary, dUnary, qUnary, wUnary, rUnary,
      gUnary, eUnary, transportedRouteUnary, transportedNameUnary, provenancePkg,
      transportedPkg⟩

end BEDC.Derived.FareySequenceUp
