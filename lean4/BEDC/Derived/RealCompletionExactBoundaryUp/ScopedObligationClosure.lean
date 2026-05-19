import BEDC.Derived.RealCompletionExactBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package

namespace BEDC.Derived.RealCompletionExactBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem RealCompletionExactBoundaryScopedObligationClosure [AskSetup] [PackageSetup]
    {L K J S W R D E H C P N sealClass witnessBudget streamReg dyadicReal scopeRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont L K sealClass ->
      Cont J S witnessBudget ->
        Cont W R streamReg ->
          Cont D E dyadicReal ->
            Cont sealClass dyadicReal scopeRead ->
              PkgSig bundle scopeRead pkg ->
                realCompletionExactBoundaryFields
                    (RealCompletionExactBoundaryUp.mk L K J S W R D E H C P N) =
                  [L, K, J, S, W, R, D, E, H, C, P, N] ∧
                  Cont L K sealClass ∧
                    Cont J S witnessBudget ∧
                      Cont W R streamReg ∧
                        Cont D E dyadicReal ∧
                          Cont sealClass dyadicReal scopeRead ∧
                            PkgSig bundle scopeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig
  intro sealRoute witnessRoute streamRoute dyadicRoute scopeRoute scopePkg
  exact ⟨rfl, sealRoute, witnessRoute, streamRoute, dyadicRoute, scopeRoute, scopePkg⟩

end BEDC.Derived.RealCompletionExactBoundaryUp
