import BEDC.Derived.CauchyTailModulusSealUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyTailModulusSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyTailModulusSeal_nonescape [AskSetup] [PackageSetup]
    {M F X tau D W0 W1 Q0 Q1 E H C P N thresholdRead windowRead sealRead publicRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ->
      UnaryHistory F ->
        UnaryHistory D ->
          UnaryHistory E ->
            Cont M F thresholdRead ->
              Cont thresholdRead D windowRead ->
                Cont windowRead E sealRead ->
                  Cont sealRead E publicRead ->
                    PkgSig bundle publicRead pkg ->
                      cauchyTailModulusSealFields
                          (CauchyTailModulusSealUp.mk M F X tau D W0 W1 Q0 Q1 E H C P N) =
                        [M, F, X, tau, D, W0, W1, Q0, Q1, E, H, C, P, N] ∧
                        UnaryHistory thresholdRead ∧ UnaryHistory windowRead ∧
                          UnaryHistory sealRead ∧ UnaryHistory publicRead ∧
                            Cont M F thresholdRead ∧ Cont thresholdRead D windowRead ∧
                              Cont windowRead E sealRead ∧ Cont sealRead E publicRead ∧
                                PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont UnaryHistory
  intro unaryM unaryF unaryD unaryE thresholdRoute windowRoute sealRoute publicRoute
    publicPkg
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed unaryM unaryF thresholdRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed thresholdUnary unaryD windowRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary unaryE sealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary unaryE publicRoute
  exact
    ⟨rfl, thresholdUnary, windowUnary, sealUnary, publicUnary, thresholdRoute,
      windowRoute, sealRoute, publicRoute, publicPkg⟩

end BEDC.Derived.CauchyTailModulusSealUp
