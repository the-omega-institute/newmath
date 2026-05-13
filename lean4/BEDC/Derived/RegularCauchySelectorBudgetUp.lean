import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

/-!
# RegularCauchySelectorBudgetUp finite tail-precision surface.
-/

namespace BEDC.Derived.RegularCauchySelectorBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchySelectorBudgetTailPrecisionSource [AskSetup] [PackageSetup]
    (mu w s r d e h c p n : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory mu ∧ UnaryHistory w ∧ UnaryHistory s ∧ UnaryHistory r ∧
    UnaryHistory d ∧ UnaryHistory e ∧ UnaryHistory h ∧ UnaryHistory c ∧
      UnaryHistory p ∧ UnaryHistory n ∧ Cont d mu w ∧ Cont w s r ∧
        Cont r e c ∧ PkgSig bundle p pkg

theorem RegularCauchySelectorBudgetCarrier_tail_precision_exactness [AskSetup]
    [PackageSetup]
    {mu w s r d e h c p n endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySelectorBudgetTailPrecisionSource mu w s r d e h c p n bundle pkg ->
      Cont h c endpoint ->
        UnaryHistory endpoint ∧ Cont d mu w ∧ Cont w s r ∧ Cont r e c ∧
          Cont h c endpoint ∧ PkgSig bundle p pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro source endpointRoute
  obtain ⟨_muUnary, _wUnary, _sUnary, _rUnary, _dUnary, _eUnary, hUnary, cUnary,
    _pUnary, _nUnary, precisionWindow, windowStream, regseqSeal, pkgSig⟩ := source
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed hUnary cUnary endpointRoute
  exact ⟨endpointUnary, precisionWindow, windowStream, regseqSeal, endpointRoute, pkgSig⟩

end BEDC.Derived.RegularCauchySelectorBudgetUp
