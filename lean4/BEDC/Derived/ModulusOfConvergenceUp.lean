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
    (precision selector modulus schedule witness ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory selector ∧ UnaryHistory modulus ∧
    UnaryHistory schedule ∧ UnaryHistory witness ∧ UnaryHistory ledger ∧
      UnaryHistory provenance ∧ Cont precision selector modulus ∧
        Cont modulus schedule witness ∧ Cont witness ledger provenance ∧
          PkgSig bundle provenance pkg

theorem ModulusOfConvergencePacket_tail_restriction_stability [AskSetup] [PackageSetup]
    {precision selector modulus schedule witness ledger provenance schedule' witness'
      provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModulusOfConvergencePacket precision selector modulus schedule witness ledger provenance
        bundle pkg ->
      hsame schedule schedule' ->
        hsame witness witness' ->
          hsame provenance provenance' ->
            Cont modulus schedule' witness' ->
              Cont witness' ledger provenance' ->
                PkgSig bundle provenance' pkg ->
                  ModulusOfConvergencePacket precision selector modulus schedule' witness'
                      ledger provenance' bundle pkg ∧
                    hsame witness witness' ∧ hsame provenance provenance' := by
  intro packet sameSchedule sameWitness sameProvenance restrictedWitness restrictedProvenance
    restrictedPkg
  have precisionUnary : UnaryHistory precision :=
    packet.left
  have selectorUnary : UnaryHistory selector :=
    packet.right.left
  have modulusUnary : UnaryHistory modulus :=
    packet.right.right.left
  have scheduleUnary : UnaryHistory schedule' :=
    unary_transport packet.right.right.right.left sameSchedule
  have witnessUnary : UnaryHistory witness' :=
    unary_transport packet.right.right.right.right.left sameWitness
  have ledgerUnary : UnaryHistory ledger :=
    packet.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance' :=
    unary_transport packet.right.right.right.right.right.right.left sameProvenance
  have modulusRoute : Cont precision selector modulus :=
    packet.right.right.right.right.right.right.right.left
  constructor
  · exact
      And.intro precisionUnary
        (And.intro selectorUnary
          (And.intro modulusUnary
            (And.intro scheduleUnary
              (And.intro witnessUnary
                (And.intro ledgerUnary
                  (And.intro provenanceUnary
                    (And.intro modulusRoute
                      (And.intro restrictedWitness
                        (And.intro restrictedProvenance restrictedPkg)))))))))
  · exact And.intro sameWitness sameProvenance

end BEDC.Derived.ModulusOfConvergenceUp
