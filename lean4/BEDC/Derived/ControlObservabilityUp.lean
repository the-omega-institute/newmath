import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ControlObservabilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ControlObservabilityCarrier [AskSetup] [PackageSetup]
    (state transition output observation stack trace provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory transition ∧ UnaryHistory output ∧
    UnaryHistory observation ∧ UnaryHistory stack ∧ UnaryHistory trace ∧
      UnaryHistory provenance ∧ UnaryHistory endpoint ∧ Cont transition output observation ∧
        Cont observation stack trace ∧ Cont trace provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem ControlObservabilityCarrier_finite_trace_ledger_readback [AskSetup] [PackageSetup]
    {state transition output observation stack trace provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ControlObservabilityCarrier state transition output observation stack trace provenance endpoint
        bundle pkg ->
      UnaryHistory observation ∧ UnaryHistory stack ∧ UnaryHistory trace ∧
        UnaryHistory endpoint ∧ Cont transition output observation ∧ Cont observation stack trace ∧
          Cont trace provenance endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  exact
    And.intro carrier.right.right.right.left
      (And.intro carrier.right.right.right.right.left
        (And.intro carrier.right.right.right.right.right.left
          (And.intro carrier.right.right.right.right.right.right.right.left
            (And.intro carrier.right.right.right.right.right.right.right.right.left
              (And.intro carrier.right.right.right.right.right.right.right.right.right.left
                (And.intro carrier.right.right.right.right.right.right.right.right.right.right.left
                  carrier.right.right.right.right.right.right.right.right.right.right.right))))))

end BEDC.Derived.ControlObservabilityUp
