import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TauberianRemainderUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TauberianRemainderCarrier [AskSetup] [PackageSetup]
    (A H T D R E K C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory A ∧ UnaryHistory H ∧ UnaryHistory T ∧ UnaryHistory D ∧
    UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory K ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont A H T ∧ Cont T D R ∧ Cont R E C ∧
        Cont K C P ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem TauberianRemainderCarrier_real_seal_nonescape [AskSetup] [PackageSetup]
    {A H T D R E K C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TauberianRemainderCarrier A H T D R E K C P N bundle pkg →
      UnaryHistory A ∧ UnaryHistory H ∧ UnaryHistory T ∧ UnaryHistory D ∧
        UnaryHistory R ∧ UnaryHistory E ∧ Cont A H T ∧ Cont T D R ∧ Cont R E C ∧
          PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig
  intro carrier
  obtain ⟨aUnary, hUnary, tUnary, dUnary, rUnary, eUnary, _kUnary, _cUnary, _pUnary,
    _nUnary, abelCesaroRow, dyadicReadbackRow, realSealRow, _transportRow, pPkg,
    nPkg⟩ := carrier
  exact
    ⟨aUnary, hUnary, tUnary, dUnary, rUnary, eUnary, abelCesaroRow, dyadicReadbackRow,
      realSealRow, pPkg, nPkg⟩

end BEDC.Derived.TauberianRemainderUp
