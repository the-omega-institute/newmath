import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyInterleaveUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyInterleaveCarrier [AskSetup] [PackageSetup]
    (I J S T W D M H C P N endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory I ∧ UnaryHistory J ∧ UnaryHistory S ∧ UnaryHistory T ∧
    UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory M ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ UnaryHistory endpoint ∧
        Cont I S T ∧ Cont T W D ∧ Cont D M endpoint ∧ PkgSig bundle endpoint pkg

theorem RegularCauchyInterleaveWindowMergeExactness [AskSetup] [PackageSetup]
    {I J S T W D M H C P N endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyInterleaveCarrier I J S T W D M H C P N endpoint bundle pkg ->
      UnaryHistory I ∧ UnaryHistory J ∧ UnaryHistory S ∧ UnaryHistory T ∧
        UnaryHistory W ∧ UnaryHistory D ∧ Cont I S T ∧ Cont T W D ∧
          Cont D M endpoint ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier
  obtain ⟨iUnary, jUnary, sUnary, tUnary, wUnary, dUnary, _mUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _endpointUnary, sourceWindow, windowDyadic,
    dyadicHandoff, pkgSig⟩ := carrier
  exact
    ⟨iUnary, jUnary, sUnary, tUnary, wUnary, dUnary, sourceWindow, windowDyadic,
      dyadicHandoff, pkgSig⟩

end BEDC.Derived.RegularCauchyInterleaveUp
