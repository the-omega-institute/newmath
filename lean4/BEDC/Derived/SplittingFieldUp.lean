import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SplittingFieldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SplittingFieldRootCarrierPacket [AskSetup] [PackageSetup]
    (fieldExt polynomial roots factors transport provenance classifier factorLedger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory fieldExt ∧ UnaryHistory polynomial ∧ UnaryHistory roots ∧
    UnaryHistory factors ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
      Cont fieldExt polynomial classifier ∧ Cont roots factors factorLedger ∧
        Cont provenance factorLedger endpoint ∧ PkgSig bundle endpoint pkg

theorem SplittingFieldRootCarrierPacket_classifier_obligation [AskSetup] [PackageSetup]
    {fieldExt polynomial roots factors transport provenance classifier factorLedger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SplittingFieldRootCarrierPacket fieldExt polynomial roots factors transport provenance
        classifier factorLedger endpoint bundle pkg ->
      UnaryHistory fieldExt ∧ UnaryHistory polynomial ∧ UnaryHistory roots ∧
        UnaryHistory factors ∧ UnaryHistory transport ∧ UnaryHistory classifier ∧
          Cont fieldExt polynomial classifier ∧ Cont roots factors factorLedger ∧
            hsame endpoint (append provenance factorLedger) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have classifierRow : Cont fieldExt polynomial classifier :=
    packet.right.right.right.right.right.right.left
  have factorLedgerRow : Cont roots factors factorLedger :=
    packet.right.right.right.right.right.right.right.left
  have endpointRow : Cont provenance factorLedger endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed packet.left packet.right.left classifierRow
  have _factorLedgerUnary : UnaryHistory factorLedger :=
    unary_cont_closed packet.right.right.left packet.right.right.right.left factorLedgerRow
  exact And.intro packet.left
    (And.intro packet.right.left
      (And.intro packet.right.right.left
        (And.intro packet.right.right.right.left
          (And.intro packet.right.right.right.right.left
            (And.intro classifierUnary
              (And.intro classifierRow
                (And.intro factorLedgerRow
                  (And.intro endpointRow
                    packet.right.right.right.right.right.right.right.right.right))))))))

end BEDC.Derived.SplittingFieldUp
