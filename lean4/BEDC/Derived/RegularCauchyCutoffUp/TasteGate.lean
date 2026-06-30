import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyCutoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyCutoffCarrier [AskSetup] [PackageSetup]
    (n W R D E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory n ∧ UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory D ∧
    UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem RegularCauchyCutoffCarrier_tail_window [AskSetup] [PackageSetup]
    {n W R D E H C P N «seal» : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyCutoffCarrier n W R D E H C P N bundle pkg →
      Cont D E «seal» →
        PkgSig bundle «seal» pkg →
          UnaryHistory n ∧ UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory D ∧
            UnaryHistory E ∧ UnaryHistory «seal» ∧ Cont D E «seal» ∧
              PkgSig bundle N pkg ∧ PkgSig bundle «seal» pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier sealRoute sealPkg
  obtain ⟨nUnary, wUnary, rUnary, dUnary, eUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _pPkg, nPkg⟩ := carrier
  have sealUnary : UnaryHistory «seal» :=
    unary_cont_closed dUnary eUnary sealRoute
  exact
    ⟨nUnary, wUnary, rUnary, dUnary, eUnary, sealUnary, sealRoute, nPkg, sealPkg⟩

end BEDC.Derived.RegularCauchyCutoffUp
