import BEDC.Derived.FareySequenceUp.TasteGate

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceApproximationWindowFactorization
    [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N boundaryRead levelRead toleranceRead
      windowRead regseqRead approxRead sealedRead structuralRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg →
      Cont B A boundaryRead →
        Cont boundaryRead M levelRead →
          Cont levelRead T toleranceRead →
            Cont toleranceRead W windowRead →
              Cont windowRead R regseqRead →
                Cont regseqRead G approxRead →
                  Cont approxRead E sealedRead →
                    Cont H C structuralRead →
                      PkgSig bundle P pkg →
                        PkgSig bundle N pkg →
                          UnaryHistory boundaryRead ∧ UnaryHistory levelRead ∧
                            UnaryHistory toleranceRead ∧ UnaryHistory windowRead ∧
                              UnaryHistory regseqRead ∧ UnaryHistory approxRead ∧
                                UnaryHistory sealedRead ∧ Cont windowRead R regseqRead ∧
                                  Cont regseqRead G approxRead ∧ Cont approxRead E sealedRead ∧
                                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier boundaryRoute levelRoute toleranceRoute windowRoute regseqRoute approxRoute
    sealedRoute _structuralRoute provenancePkg namePkg
  obtain ⟨bUnary, aUnary, mUnary, _lUnary, tUnary, _sUnary, _dUnary, _qUnary,
    wUnary, rUnary, gUnary, eUnary, _hUnary, _cUnary, _pUnary, _nUnary, _aEmpty,
    _sEmpty, _mEmpty, _gEmpty, _eEmpty, _carrierPkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed bUnary aUnary boundaryRoute
  have levelUnary : UnaryHistory levelRead :=
    unary_cont_closed boundaryUnary mUnary levelRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed levelUnary tUnary toleranceRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed toleranceUnary wUnary windowRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed windowUnary rUnary regseqRoute
  have approxUnary : UnaryHistory approxRead :=
    unary_cont_closed regseqUnary gUnary approxRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed approxUnary eUnary sealedRoute
  exact
    ⟨boundaryUnary, levelUnary, toleranceUnary, windowUnary, regseqUnary, approxUnary,
      sealedUnary, regseqRoute, approxRoute, sealedRoute, provenancePkg, namePkg⟩

end BEDC.Derived.FareySequenceUp
