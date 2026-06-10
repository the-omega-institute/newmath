import BEDC.Derived.CalculusUp

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusRootFtcBoundaryRefusal [AskSetup] [PackageSetup]
    {R L C D I Q Y H T P N derivativeRead integralRead derivativeDyadic integralDyadic
      derivativeSeal integralSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D ->
      UnaryHistory I ->
        UnaryHistory Q ->
          UnaryHistory Y ->
            UnaryHistory R ->
              Cont D Q derivativeRead ->
                Cont I Q integralRead ->
                  Cont derivativeRead Y derivativeDyadic ->
                    Cont integralRead Y integralDyadic ->
                      Cont derivativeDyadic R derivativeSeal ->
                        Cont integralDyadic R integralSeal ->
                          PkgSig bundle P pkg ->
                            PkgSig bundle N pkg ->
                              UnaryHistory derivativeRead ∧
                                UnaryHistory integralRead ∧
                                  UnaryHistory derivativeDyadic ∧
                                    UnaryHistory integralDyadic ∧
                                      UnaryHistory derivativeSeal ∧
                                        UnaryHistory integralSeal ∧
                                          Cont D Q derivativeRead ∧
                                            Cont I Q integralRead ∧
                                              Cont derivativeRead Y derivativeDyadic ∧
                                                Cont integralRead Y integralDyadic ∧
                                                  Cont derivativeDyadic R derivativeSeal ∧
                                                    Cont integralDyadic R integralSeal ∧
                                                      PkgSig bundle P pkg ∧
                                                        PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro derivativeUnary integralUnary qUnary yUnary rUnary derivativeRoute integralRoute
    derivativeDyadicRoute integralDyadicRoute derivativeSealRoute integralSealRoute
    provenancePkg namePkg
  have derivativeReadUnary : UnaryHistory derivativeRead :=
    unary_cont_closed derivativeUnary qUnary derivativeRoute
  have integralReadUnary : UnaryHistory integralRead :=
    unary_cont_closed integralUnary qUnary integralRoute
  have derivativeDyadicUnary : UnaryHistory derivativeDyadic :=
    unary_cont_closed derivativeReadUnary yUnary derivativeDyadicRoute
  have integralDyadicUnary : UnaryHistory integralDyadic :=
    unary_cont_closed integralReadUnary yUnary integralDyadicRoute
  have derivativeSealUnary : UnaryHistory derivativeSeal :=
    unary_cont_closed derivativeDyadicUnary rUnary derivativeSealRoute
  have integralSealUnary : UnaryHistory integralSeal :=
    unary_cont_closed integralDyadicUnary rUnary integralSealRoute
  exact
    ⟨derivativeReadUnary, integralReadUnary, derivativeDyadicUnary, integralDyadicUnary,
      derivativeSealUnary, integralSealUnary, derivativeRoute, integralRoute,
      derivativeDyadicRoute, integralDyadicRoute, derivativeSealRoute, integralSealRoute,
      provenancePkg, namePkg⟩

end BEDC.Derived.CalculusUp
