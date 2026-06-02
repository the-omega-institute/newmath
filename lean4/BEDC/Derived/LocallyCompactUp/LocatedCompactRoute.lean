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

theorem LocallyCompactLocatedCompactRoute [AskSetup] [PackageSetup]
    {metricSource point radius closedBall compactWitness locatedHandoff locatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metricSource ->
      UnaryHistory point ->
        UnaryHistory radius ->
          UnaryHistory locatedHandoff ->
            Cont metricSource point closedBall ->
              Cont closedBall radius compactWitness ->
                Cont compactWitness locatedHandoff locatedRead ->
                  PkgSig bundle locatedRead pkg ->
                    UnaryHistory closedBall ∧ UnaryHistory compactWitness ∧
                      UnaryHistory locatedRead ∧
                        hsame locatedRead (append compactWitness locatedHandoff) ∧
                          PkgSig bundle locatedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory append
  intro metricUnary pointUnary radiusUnary locatedUnary closedBallRoute compactRoute
    locatedRoute locatedPkg
  have closedBallUnary : UnaryHistory closedBall :=
    unary_cont_closed metricUnary pointUnary closedBallRoute
  have compactUnary : UnaryHistory compactWitness :=
    unary_cont_closed closedBallUnary radiusUnary compactRoute
  have locatedReadUnary : UnaryHistory locatedRead :=
    unary_cont_closed compactUnary locatedUnary locatedRoute
  have locatedReadExact : hsame locatedRead (append compactWitness locatedHandoff) := by
    cases locatedRoute
    exact hsame_refl _
  exact ⟨closedBallUnary, compactUnary, locatedReadUnary, locatedReadExact, locatedPkg⟩

end BEDC.Derived.LocallyCompactUp
