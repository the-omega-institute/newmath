import BEDC.Derived.NumFieldUp
import BEDC.FKernel.Package.Core

namespace BEDC.Derived.RingOfIntegersUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.NumFieldUp

def RingOfIntegersDedekindSourceCarrier [AskSetup] [PackageSetup]
    (numfield embeddedInt embedding equationLedger classifier provenance contLedger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  NumFieldRatReflexiveCarrier numfield ∧ UnaryHistory embeddedInt ∧ UnaryHistory embedding ∧
    UnaryHistory equationLedger ∧ UnaryHistory classifier ∧ UnaryHistory provenance ∧
      Cont numfield embeddedInt embedding ∧ Cont embedding equationLedger contLedger ∧
        Cont provenance contLedger endpoint ∧ PkgSig bundle endpoint pkg

theorem RingOfIntegersDedekindSourceCarrier_dependency_projection_boundary [AskSetup]
    [PackageSetup]
    {numfield embeddedInt embedding equationLedger classifier provenance contLedger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RingOfIntegersDedekindSourceCarrier numfield embeddedInt embedding equationLedger
      classifier provenance contLedger endpoint bundle pkg ->
      NumFieldRatReflexiveCarrier numfield ∧ UnaryHistory embeddedInt ∧
        UnaryHistory embedding ∧ UnaryHistory equationLedger ∧ UnaryHistory classifier ∧
          UnaryHistory contLedger ∧ UnaryHistory endpoint ∧ Cont numfield embeddedInt embedding ∧
            Cont embedding equationLedger contLedger ∧ Cont provenance contLedger endpoint ∧
              PkgSig bundle endpoint pkg := by
  intro carrier
  have contLedgerUnary : UnaryHistory contLedger :=
    unary_cont_closed carrier.right.right.left carrier.right.right.right.left
      carrier.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed carrier.right.right.right.right.right.left contLedgerUnary
      carrier.right.right.right.right.right.right.right.right.left
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.right.right.left
        (And.intro carrier.right.right.right.left
          (And.intro carrier.right.right.right.right.left
            (And.intro contLedgerUnary
              (And.intro endpointUnary
                (And.intro carrier.right.right.right.right.right.right.left
                  (And.intro carrier.right.right.right.right.right.right.right.left
                    (And.intro carrier.right.right.right.right.right.right.right.right.left
                      carrier.right.right.right.right.right.right.right.right.right)))))))))

end BEDC.Derived.RingOfIntegersUp
