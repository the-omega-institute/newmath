import BEDC.Derived.LocallyCompactUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocallyCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocallyCompactCompactBallWindow [AskSetup] [PackageSetup]
    {metricSource point radius closedBall compactWitness locatedHandoff compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metricSource ->
      UnaryHistory point ->
        UnaryHistory radius ->
          UnaryHistory compactWitness ->
            Cont metricSource point closedBall ->
              Cont closedBall radius compactRead ->
                Cont compactRead compactWitness locatedHandoff ->
                  PkgSig bundle compactRead pkg ->
                    UnaryHistory closedBall ∧ UnaryHistory compactRead ∧
                      hsame compactRead (append closedBall radius) ∧
                        PkgSig bundle compactRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory append
  intro metricUnary pointUnary radiusUnary _compactUnary closedBallRoute compactReadRoute
    _handoffRoute compactPkg
  have closedBallUnary : UnaryHistory closedBall :=
    unary_cont_closed metricUnary pointUnary closedBallRoute
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed closedBallUnary radiusUnary compactReadRoute
  have compactReadExact : hsame compactRead (append closedBall radius) := by
    cases compactReadRoute
    exact hsame_refl _
  exact ⟨closedBallUnary, compactReadUnary, compactReadExact, compactPkg⟩

end BEDC.Derived.LocallyCompactUp
