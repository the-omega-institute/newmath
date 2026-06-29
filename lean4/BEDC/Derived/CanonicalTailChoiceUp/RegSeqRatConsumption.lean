import BEDC.Derived.CanonicalTailChoiceUp.Nonescape
import BEDC.FKernel.Cont

namespace BEDC.Derived.CanonicalTailChoiceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CanonicalTailChoiceCarrier_regseqrat_consumption [AskSetup] [PackageSetup]
    {M E I T S R H C0 P N regseqTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CanonicalTailChoiceCarrier M E I T S R H C0 P N bundle pkg →
      Cont I T regseqTail →
        PkgSig bundle regseqTail pkg →
          UnaryHistory M ∧ UnaryHistory E ∧ UnaryHistory I ∧ UnaryHistory T ∧
            UnaryHistory regseqTail ∧ Cont I T regseqTail ∧ PkgSig bundle N pkg ∧
              PkgSig bundle regseqTail pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier regseqRoute regseqPkg
  obtain ⟨mUnary, eUnary, iUnary, tUnary, _sUnary, _rUnary, _hUnary, _c0Unary,
    _pUnary, _nUnary, _pPkg, nPkg⟩ := carrier
  have regseqUnary : UnaryHistory regseqTail :=
    unary_cont_closed iUnary tUnary regseqRoute
  exact
    ⟨mUnary, eUnary, iUnary, tUnary, regseqUnary, regseqRoute, nPkg, regseqPkg⟩

end BEDC.Derived.CanonicalTailChoiceUp
