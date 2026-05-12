import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ModulusOfConvergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ModulusOfConvergencePacket [AskSetup] [PackageSetup]
    (precision threshold modulus schedule witness ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory threshold ∧ UnaryHistory modulus ∧
    UnaryHistory schedule ∧ UnaryHistory witness ∧ Cont precision threshold modulus ∧
      Cont modulus schedule witness ∧ Cont witness ledger provenance ∧ PkgSig bundle provenance pkg

theorem ModulusOfConvergencePacket_composition_stability [AskSetup] [PackageSetup]
    {precision threshold modulus schedule witness ledger provenance precision' threshold' modulus'
      schedule' witness' ledger' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModulusOfConvergencePacket precision threshold modulus schedule witness ledger provenance bundle pkg ->
      hsame precision precision' ->
        hsame threshold threshold' ->
          hsame schedule schedule' ->
            hsame ledger ledger' ->
              Cont precision' threshold' modulus' ->
                Cont modulus' schedule' witness' ->
                  Cont witness' ledger' provenance' ->
                    PkgSig bundle provenance' pkg ->
                      ModulusOfConvergencePacket precision' threshold' modulus' schedule' witness'
                          ledger' provenance' bundle pkg ∧
                        hsame modulus modulus' ∧ hsame witness witness' ∧
                          hsame provenance provenance' := by
  intro packet samePrecision sameThreshold sameSchedule sameLedger modulusRow' witnessRow'
    provenanceRow' pkgSig'
  have precisionUnary : UnaryHistory precision :=
    packet.left
  have thresholdUnary : UnaryHistory threshold :=
    packet.right.left
  have scheduleUnary : UnaryHistory schedule :=
    packet.right.right.right.left
  have modulusRow : Cont precision threshold modulus :=
    packet.right.right.right.right.right.left
  have witnessRow : Cont modulus schedule witness :=
    packet.right.right.right.right.right.right.left
  have provenanceRow : Cont witness ledger provenance :=
    packet.right.right.right.right.right.right.right.left
  have precisionUnary' : UnaryHistory precision' :=
    unary_transport precisionUnary samePrecision
  have thresholdUnary' : UnaryHistory threshold' :=
    unary_transport thresholdUnary sameThreshold
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have modulusUnary' : UnaryHistory modulus' :=
    unary_cont_closed precisionUnary' thresholdUnary' modulusRow'
  have witnessUnary' : UnaryHistory witness' :=
    unary_cont_closed modulusUnary' scheduleUnary' witnessRow'
  have sameModulus : hsame modulus modulus' :=
    cont_respects_hsame samePrecision sameThreshold modulusRow modulusRow'
  have sameWitness : hsame witness witness' :=
    cont_respects_hsame sameModulus sameSchedule witnessRow witnessRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameWitness sameLedger provenanceRow provenanceRow'
  exact And.intro
    (And.intro precisionUnary'
      (And.intro thresholdUnary'
        (And.intro modulusUnary'
          (And.intro scheduleUnary'
            (And.intro witnessUnary'
              (And.intro modulusRow'
                (And.intro witnessRow'
                  (And.intro provenanceRow' pkgSig'))))))))
    (And.intro sameModulus (And.intro sameWitness sameProvenance))

end BEDC.Derived.ModulusOfConvergenceUp
