import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PinGroupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PinGroupReflectionExtensionCarrier [AskSetup] [PackageSetup]
    (clifford spin reflection parity action provenance ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory clifford ∧ UnaryHistory spin ∧ UnaryHistory reflection ∧
    UnaryHistory parity ∧ Cont reflection parity action ∧ Cont provenance action ledger ∧
      Cont ledger spin endpoint ∧ PkgSig bundle endpoint pkg

theorem PinGroupReflectionExtensionCarrier_bhist_carrier_obligation [AskSetup] [PackageSetup]
    {clifford spin reflection parity action provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PinGroupReflectionExtensionCarrier clifford spin reflection parity action provenance ledger
        endpoint bundle pkg ->
      UnaryHistory clifford ∧ UnaryHistory spin ∧ UnaryHistory reflection ∧
        UnaryHistory parity ∧ Cont reflection parity action ∧ Cont provenance action ledger ∧
          Cont ledger spin endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.right.right.left
        (And.intro carrier.right.right.right.left
          (And.intro carrier.right.right.right.right.left
            (And.intro carrier.right.right.right.right.right.left
              (And.intro carrier.right.right.right.right.right.right.left
                carrier.right.right.right.right.right.right.right))))))

end BEDC.Derived.PinGroupUp
