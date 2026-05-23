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

theorem CauchyTailModulusSeal_public_classifier_route [AskSetup] [PackageSetup]
    {M F X tau D W0 W1 Q0 Q1 E H C P N thresholdRead windowRead readback0 readback1
      pairedRead sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M →
      UnaryHistory F →
        UnaryHistory D →
          UnaryHistory W0 →
            UnaryHistory W1 →
              UnaryHistory Q0 →
                UnaryHistory Q1 →
                  UnaryHistory E →
                    UnaryHistory X →
                      Cont M F thresholdRead →
                        Cont thresholdRead D windowRead →
                          Cont W0 Q0 readback0 →
                            Cont W1 Q1 readback1 →
                              Cont readback0 readback1 pairedRead →
                                Cont pairedRead E sealRead →
                                  Cont X sealRead publicRead →
                                    PkgSig bundle publicRead pkg →
                                      cauchyTailModulusSealFields
                                          (CauchyTailModulusSealUp.mk M F X tau D W0 W1
                                            Q0 Q1 E H C P N) =
                                        [M, F, X, tau, D, W0, W1, Q0, Q1, E, H, C,
                                          P, N] ∧
                                        UnaryHistory thresholdRead ∧
                                          UnaryHistory windowRead ∧
                                            UnaryHistory readback0 ∧
                                              UnaryHistory readback1 ∧
                                                UnaryHistory pairedRead ∧
                                                  UnaryHistory sealRead ∧
                                                    UnaryHistory publicRead ∧
                                                      PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro modulusUnary fusionUnary dyadicUnary window0Unary window1Unary readback0Unary
    readback1Unary realSealUnary extractorUnary thresholdRoute windowRoute readback0Route
    readback1Route pairedRoute sealRoute publicRoute publicPkg
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed modulusUnary fusionUnary thresholdRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed thresholdUnary dyadicUnary windowRoute
  have readback0Unary' : UnaryHistory readback0 :=
    unary_cont_closed window0Unary readback0Unary readback0Route
  have readback1Unary' : UnaryHistory readback1 :=
    unary_cont_closed window1Unary readback1Unary readback1Route
  have pairedUnary : UnaryHistory pairedRead :=
    unary_cont_closed readback0Unary' readback1Unary' pairedRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed pairedUnary realSealUnary sealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed extractorUnary sealUnary publicRoute
  exact
    ⟨rfl, thresholdUnary, windowUnary, readback0Unary', readback1Unary', pairedUnary,
      sealUnary, publicUnary, publicPkg⟩

end BEDC.Derived.CauchyTailModulusSealUp
