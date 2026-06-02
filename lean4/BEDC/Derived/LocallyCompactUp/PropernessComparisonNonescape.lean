import BEDC.Derived.LocallyCompactUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocallyCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocallyCompactPropernessComparisonNonescape [AskSetup] [PackageSetup]
    {metricSource point radius closedBall compactWitness properRead hostTail : BHist} :
    UnaryHistory metricSource →
      UnaryHistory point →
        UnaryHistory radius →
          Cont metricSource point closedBall →
            Cont closedBall radius compactWitness →
              Cont closedBall compactWitness properRead →
                UnaryHistory properRead ∧
                  hsame properRead (append closedBall compactWitness) ∧
                    (Cont properRead (BHist.e0 hostTail) metricSource -> False) ∧
                      (Cont properRead (BHist.e1 hostTail) metricSource -> False) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory Pkg AskSetup PackageSetup
  intro metricUnary pointUnary radiusUnary closedBallRoute compactRoute properRoute
  have closedBallUnary : UnaryHistory closedBall :=
    unary_cont_closed metricUnary pointUnary closedBallRoute
  have compactUnary : UnaryHistory compactWitness :=
    unary_cont_closed closedBallUnary radiusUnary compactRoute
  have properUnary : UnaryHistory properRead :=
    unary_cont_closed closedBallUnary compactUnary properRoute
  have sourceToProper : Cont metricSource (append point compactWitness) properRead := by
    cases closedBallRoute
    exact properRoute.trans (append_assoc metricSource point compactWitness)
  exact
    ⟨properUnary, properRoute,
      (fun back => cont_mutual_extension_right_tail_absurd.left sourceToProper back),
      (fun back => cont_mutual_extension_right_tail_absurd.right sourceToProper back)⟩

end BEDC.Derived.LocallyCompactUp
