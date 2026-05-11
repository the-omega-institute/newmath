import BEDC.Derived.CauchyModulusUp

namespace BEDC.Derived.CauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusPacket_window_composition_handoff [AskSetup] [PackageSetup]
    {precision threshold tolerance schedule observationLedger consumptionLedger window endpoint
      handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusPacket precision threshold tolerance schedule observationLedger consumptionLedger
        window endpoint bundle pkg ->
      Cont endpoint consumptionLedger handoff ->
        UnaryHistory handoff ∧
          Cont precision threshold schedule ∧
            Cont schedule tolerance observationLedger ∧
              Cont observationLedger consumptionLedger window ∧
                Cont window threshold endpoint ∧
                  Cont endpoint consumptionLedger handoff ∧ PkgSig bundle endpoint pkg := by
  intro packet handoffRow
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed packet.right.right.right.right.right.right.right.left
      packet.right.right.right.right.right.left handoffRow
  exact And.intro handoffUnary
    (And.intro packet.right.right.right.right.right.right.right.right.left
      (And.intro packet.right.right.right.right.right.right.right.right.right.left
        (And.intro packet.right.right.right.right.right.right.right.right.right.right.left
          (And.intro packet.right.right.right.right.right.right.right.right.right.right.right.left
            (And.intro handoffRow
              packet.right.right.right.right.right.right.right.right.right.right.right.right)))))

end BEDC.Derived.CauchyModulusUp
