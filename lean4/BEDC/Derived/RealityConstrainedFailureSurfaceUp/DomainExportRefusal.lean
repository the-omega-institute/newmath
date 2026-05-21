import BEDC.Derived.RealityConstrainedFailureSurfaceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RealityConstrainedFailureSurfaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealityConstrainedFailureSurfaceDomainExportRefusal [AskSetup] [PackageSetup]
    {O D K U L H C P N domainRead mismatchRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont O D domainRead →
      Cont K U mismatchRead →
        Cont domainRead mismatchRead exportRead →
          UnaryHistory O →
            UnaryHistory D →
              UnaryHistory K →
                UnaryHistory U →
                  PkgSig bundle exportRead pkg →
                    realityConstrainedFailureSurfaceFields
                        (RealityConstrainedFailureSurfaceUp.mk O D K U L H C P N) =
                      [O, D, K, U, L, H, C, P, N] ∧
                      UnaryHistory domainRead ∧ UnaryHistory mismatchRead ∧
                        UnaryHistory exportRead ∧ Cont O D domainRead ∧
                          Cont K U mismatchRead ∧ Cont domainRead mismatchRead exportRead ∧
                            PkgSig bundle exportRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro domainRoute mismatchRoute exportRoute unaryO unaryD unaryK unaryU exportPkg
  have domainUnary : UnaryHistory domainRead :=
    unary_cont_closed unaryO unaryD domainRoute
  have mismatchUnary : UnaryHistory mismatchRead :=
    unary_cont_closed unaryK unaryU mismatchRoute
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed domainUnary mismatchUnary exportRoute
  exact
    ⟨rfl, domainUnary, mismatchUnary, exportUnary, domainRoute, mismatchRoute, exportRoute,
      exportPkg⟩

end BEDC.Derived.RealityConstrainedFailureSurfaceUp
