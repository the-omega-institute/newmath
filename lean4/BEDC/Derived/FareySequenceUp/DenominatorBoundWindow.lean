import BEDC.Derived.FareySequenceUp.TasteGate

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceCarrier_denominator_bound_window [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N budgetRead mediantRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg →
      Cont L T budgetRead →
        Cont budgetRead M mediantRead →
          PkgSig bundle mediantRead pkg →
            UnaryHistory L ∧ UnaryHistory T ∧ UnaryHistory M ∧
              UnaryHistory budgetRead ∧ UnaryHistory mediantRead ∧
                Cont L T budgetRead ∧ Cont budgetRead M mediantRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle mediantRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier levelToleranceBudget budgetMediantRead mediantPkg
  obtain ⟨_bUnary, _aUnary, mUnary, lUnary, tUnary, _sUnary, _dUnary, _qUnary,
    _wUnary, _rUnary, _gUnary, _eUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _aEmpty, _sEmpty, _mEmpty, _gEmpty, _eEmpty, provenancePkg⟩ := carrier
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed lUnary tUnary levelToleranceBudget
  have mediantUnary : UnaryHistory mediantRead :=
    unary_cont_closed budgetUnary mUnary budgetMediantRead
  exact
    ⟨lUnary, tUnary, mUnary, budgetUnary, mediantUnary, levelToleranceBudget,
      budgetMediantRead, provenancePkg, mediantPkg⟩

end BEDC.Derived.FareySequenceUp
