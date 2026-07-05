import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteCauchyDensityNetCarrier [AskSetup] [PackageSetup]
    (D W R E M T C P L : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory E ∧
    UnaryHistory M ∧ UnaryHistory T ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory L ∧ PkgSig bundle L pkg

theorem FiniteCauchyDensityNetCarrier_obligation_carrier [AskSetup] [PackageSetup]
    {D W R E M T C P L densityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteCauchyDensityNetCarrier D W R E M T C P L bundle pkg ->
      Cont D W R ->
        Cont R E M ->
          Cont M T densityRead ->
            PkgSig bundle densityRead pkg ->
              UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory E ∧
                UnaryHistory M ∧ UnaryHistory T ∧ UnaryHistory C ∧ UnaryHistory P ∧
                  UnaryHistory L ∧ UnaryHistory densityRead ∧ Cont D W R ∧
                    Cont R E M ∧ Cont M T densityRead ∧
                      PkgSig bundle densityRead pkg := by
  -- BEDC touchpoint anchor: FiniteCauchyDensityNetCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier densityRoute readbackRoute sealRoute densityPkg
  obtain ⟨dUnary, wUnary, _rUnary, eUnary, _mUnary, tUnary, cUnary, pUnary, lUnary,
    _localPkg⟩ := carrier
  have routeRUnary : UnaryHistory R :=
    unary_cont_closed dUnary wUnary densityRoute
  have routeMUnary : UnaryHistory M :=
    unary_cont_closed routeRUnary eUnary readbackRoute
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed routeMUnary tUnary sealRoute
  exact
    ⟨dUnary, wUnary, routeRUnary, eUnary, routeMUnary, tUnary, cUnary, pUnary,
      lUnary, densityUnary, densityRoute, readbackRoute, sealRoute, densityPkg⟩

end BEDC.Derived
