import BEDC.Derived.CaratheodoryKernelConvergenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CaratheodoryKernelConvergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CaratheodoryKernelConvergenceCarrier_normal_family_handoff [AskSetup] [PackageSetup]
    {D E H N R T C P L compactRead holomorphicRead normalRead riemannRead namedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D ->
      UnaryHistory E ->
        UnaryHistory H ->
          UnaryHistory N ->
            UnaryHistory R ->
              UnaryHistory T ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory L ->
                      Cont D E compactRead ->
                        Cont compactRead H holomorphicRead ->
                          Cont holomorphicRead N normalRead ->
                            Cont normalRead R riemannRead ->
                              Cont C L namedRead ->
                                PkgSig bundle P pkg ->
                                  PkgSig bundle L pkg ->
                                    UnaryHistory compactRead ∧
                                      UnaryHistory holomorphicRead ∧
                                        UnaryHistory normalRead ∧
                                          UnaryHistory riemannRead ∧
                                            UnaryHistory namedRead ∧
                                              Cont D E compactRead ∧
                                                Cont compactRead H holomorphicRead ∧
                                                  Cont holomorphicRead N normalRead ∧
                                                    Cont normalRead R riemannRead ∧
                                                      Cont C L namedRead ∧
                                                        PkgSig bundle P pkg ∧
                                                          PkgSig bundle L pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro DUnary EUnary HUnary NUnary RUnary _TUnary CUnary _PUnary LUnary compactRoute
    holomorphicRoute normalRoute riemannRoute namedRoute provenancePkg namePkg
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed DUnary EUnary compactRoute
  have holomorphicReadUnary : UnaryHistory holomorphicRead :=
    unary_cont_closed compactReadUnary HUnary holomorphicRoute
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed holomorphicReadUnary NUnary normalRoute
  have riemannReadUnary : UnaryHistory riemannRead :=
    unary_cont_closed normalReadUnary RUnary riemannRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed CUnary LUnary namedRoute
  exact
    ⟨compactReadUnary, holomorphicReadUnary, normalReadUnary, riemannReadUnary,
      namedReadUnary, compactRoute, holomorphicRoute, normalRoute, riemannRoute,
      namedRoute, provenancePkg, namePkg⟩

end BEDC.Derived.CaratheodoryKernelConvergenceUp
