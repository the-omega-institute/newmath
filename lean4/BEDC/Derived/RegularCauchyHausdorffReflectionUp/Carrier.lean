import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyHausdorffReflectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyHausdorffReflectionCarrier [AskSetup] [PackageSetup]
    (X Y S T D U E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory X ∧
    UnaryHistory Y ∧
      UnaryHistory S ∧
        UnaryHistory T ∧
          UnaryHistory D ∧
            UnaryHistory U ∧
              UnaryHistory E ∧
                UnaryHistory H ∧
                  UnaryHistory C ∧
                    UnaryHistory P ∧
                      UnaryHistory N ∧ PkgSig bundle P pkg

theorem RegularCauchyHausdorffReflectionCarrier_admission_surface
    [AskSetup] [PackageSetup]
    {X Y S T D U E H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyHausdorffReflectionCarrier X Y S T D U E H C P N bundle pkg →
      UnaryHistory X ∧
        UnaryHistory Y ∧
          UnaryHistory S ∧
            UnaryHistory T ∧
              UnaryHistory D ∧
                UnaryHistory U ∧
                  UnaryHistory E ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier
  exact
    ⟨carrier.left,
      carrier.right.left,
      carrier.right.right.left,
      carrier.right.right.right.left,
      carrier.right.right.right.right.left,
      carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.RegularCauchyHausdorffReflectionUp
