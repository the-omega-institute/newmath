import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.GapClosureBoundaryUp.TasteGate

namespace BEDC.Derived.GapClosureBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem GapClosureBoundaryRefusalRouteExactness [AskSetup] [PackageSetup]
    {G S R H C P N refusal consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory G ->
      UnaryHistory R ->
        UnaryHistory C ->
          Cont G R refusal ->
            Cont refusal C consumer ->
              PkgSig bundle consumer pkg ->
                (∃ packet : GapClosureBoundaryUp,
                  packet = GapClosureBoundaryUp.mk G S R H C P N) ∧
                  UnaryHistory refusal ∧ UnaryHistory consumer ∧ Cont G R refusal ∧
                    Cont refusal C consumer ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro unaryG unaryR unaryC refusalRoute consumerRoute consumerPkg
  have refusalUnary : UnaryHistory refusal :=
    unary_cont_closed unaryG unaryR refusalRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed refusalUnary unaryC consumerRoute
  exact
    ⟨Exists.intro (GapClosureBoundaryUp.mk G S R H C P N) rfl, refusalUnary,
      consumerUnary, refusalRoute, consumerRoute, consumerPkg⟩

end BEDC.Derived.GapClosureBoundaryUp
