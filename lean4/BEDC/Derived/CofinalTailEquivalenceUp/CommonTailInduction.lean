import BEDC.Derived.CofinalTailEquivalenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CofinalTailEquivalenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CofinalTailEquivalenceCommonTailInduction [AskSetup] [PackageSetup]
    {R0 R1 W Q D A H C P N route0 route1 sharedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    cofinalTailEquivalenceFields (CofinalTailEquivalenceUp.mk R0 R1 W Q D A H C P N) =
        [R0, R1, W, Q, D, A, H, C, P, N] →
      UnaryHistory R0 →
        UnaryHistory R1 →
          UnaryHistory W →
            UnaryHistory Q →
              Cont R0 W route0 →
                Cont R1 W route1 →
                  Cont route0 Q sharedRead →
                    Cont route1 Q sharedRead →
                      PkgSig bundle sharedRead pkg →
                        UnaryHistory route0 ∧ UnaryHistory route1 ∧
                          UnaryHistory sharedRead ∧ Cont R0 W route0 ∧
                            Cont R1 W route1 ∧ Cont route0 Q sharedRead ∧
                              Cont route1 Q sharedRead ∧ PkgSig bundle sharedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro fieldProjection unaryR0 unaryR1 unaryW unaryQ route0Cont route1Cont
    sharedFromRoute0 sharedFromRoute1 sharedPkg
  have projectedFields :
      cofinalTailEquivalenceFields (CofinalTailEquivalenceUp.mk R0 R1 W Q D A H C P N) =
        [R0, R1, W, Q, D, A, H, C, P, N] :=
    fieldProjection
  cases projectedFields
  have route0Unary : UnaryHistory route0 :=
    unary_cont_closed unaryR0 unaryW route0Cont
  have route1Unary : UnaryHistory route1 :=
    unary_cont_closed unaryR1 unaryW route1Cont
  have sharedUnary : UnaryHistory sharedRead :=
    unary_cont_closed route0Unary unaryQ sharedFromRoute0
  exact
    ⟨route0Unary, route1Unary, sharedUnary, route0Cont, route1Cont, sharedFromRoute0,
      sharedFromRoute1, sharedPkg⟩

end BEDC.Derived.CofinalTailEquivalenceUp
