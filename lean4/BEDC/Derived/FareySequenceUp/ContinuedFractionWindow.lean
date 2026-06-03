import BEDC.Derived.FareySequenceUp.TasteGate

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceContinuedFractionWindow [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N rationalRead windowRead regseqRead
      continuedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg →
      Cont Q W rationalRead →
        Cont rationalRead R windowRead →
          Cont windowRead L regseqRead →
            Cont regseqRead T continuedRead →
              PkgSig bundle P pkg →
                PkgSig bundle N pkg →
                  UnaryHistory rationalRead ∧ UnaryHistory windowRead ∧
                    UnaryHistory regseqRead ∧ UnaryHistory continuedRead ∧
                      hsame rationalRead (append Q W) ∧
                        hsame windowRead (append rationalRead R) ∧
                          hsame regseqRead (append windowRead L) ∧
                            hsame continuedRead (append regseqRead T) ∧
                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle PkgSig hsame UnaryHistory
  intro carrier rationalRoute windowRoute regseqRoute continuedRoute provenancePkg namePkg
  obtain ⟨_bUnary, _aUnary, _mUnary, lUnary, tUnary, _sUnary, _dUnary, qUnary,
    wUnary, rUnary, _gUnary, _eUnary, _hUnary, _cUnary, _pUnary, _nUnary, _aEmpty,
    _sEmpty, _mEmpty, _gEmpty, _eEmpty, _carrierPkg⟩ := carrier
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed qUnary wUnary rationalRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed rationalUnary rUnary windowRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed windowUnary lUnary regseqRoute
  have continuedUnary : UnaryHistory continuedRead :=
    unary_cont_closed regseqUnary tUnary continuedRoute
  have rationalExact : hsame rationalRead (append Q W) := by
    exact rationalRoute
  have windowExact : hsame windowRead (append rationalRead R) := by
    exact windowRoute
  have regseqExact : hsame regseqRead (append windowRead L) := by
    exact regseqRoute
  have continuedExact : hsame continuedRead (append regseqRead T) := by
    exact continuedRoute
  exact
    ⟨rationalUnary, windowUnary, regseqUnary, continuedUnary, rationalExact,
      windowExact, regseqExact, continuedExact, provenancePkg, namePkg⟩

end BEDC.Derived.FareySequenceUp
