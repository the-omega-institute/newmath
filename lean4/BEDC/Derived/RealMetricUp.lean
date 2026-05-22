import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RealMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealMetricCarrier [AskSetup] [PackageSetup]
    (X Y A D S R H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory X ∧
    UnaryHistory Y ∧
      UnaryHistory A ∧
        UnaryHistory D ∧
          UnaryHistory S ∧
            UnaryHistory R ∧
              UnaryHistory H ∧
                UnaryHistory C ∧
                  UnaryHistory P ∧
                    UnaryHistory N ∧ PkgSig bundle P pkg

theorem RealMetricCarrier_absolute_value_distance_handoff [AskSetup] [PackageSetup]
    {X Y A D S R H C P N windowRead regularRead distanceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealMetricCarrier X Y A D S R H C P N bundle pkg →
      Cont X S windowRead →
        Cont windowRead R regularRead →
          Cont regularRead A distanceRead →
            PkgSig bundle distanceRead pkg →
              UnaryHistory X ∧ UnaryHistory S ∧ UnaryHistory regularRead ∧
                UnaryHistory distanceRead ∧ Cont X S windowRead ∧
                  Cont windowRead R regularRead ∧ Cont regularRead A distanceRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle distanceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier windowCont regularCont distanceCont distancePkg
  have xUnary : UnaryHistory X := carrier.left
  have sUnary : UnaryHistory S := carrier.right.right.right.right.left
  have rUnary : UnaryHistory R := carrier.right.right.right.right.right.left
  have aUnary : UnaryHistory A := carrier.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed xUnary sUnary windowCont
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary rUnary regularCont
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed regularUnary aUnary distanceCont
  exact
    ⟨xUnary, sUnary, regularUnary, distanceUnary, windowCont, regularCont, distanceCont,
      pPkg, distancePkg⟩

end BEDC.Derived.RealMetricUp
