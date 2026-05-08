import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RepresentationRingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RepresentationRingBHistRepresentationPacket [AskSetup] [PackageSetup]
    (group ring reps directSum tensor provenance classifier ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory group ∧ UnaryHistory ring ∧ UnaryHistory reps ∧ UnaryHistory directSum ∧
    UnaryHistory tensor ∧ UnaryHistory provenance ∧ UnaryHistory classifier ∧
      Cont reps directSum tensor ∧ Cont group ring provenance ∧
        Cont provenance classifier ledger ∧ Cont ledger tensor endpoint ∧
          PkgSig bundle endpoint pkg

def RepresentationRingGrothendieckClassifier
    (group0 ring0 reps0 directSum0 tensor0 provenance0 classifier0 ledger0 endpoint0
      group1 ring1 reps1 directSum1 tensor1 provenance1 classifier1 ledger1 endpoint1 : BHist) :
    Prop :=
  hsame group0 group1 ∧ hsame ring0 ring1 ∧ hsame reps0 reps1 ∧
    hsame directSum0 directSum1 ∧ hsame tensor0 tensor1 ∧
      hsame provenance0 provenance1 ∧ hsame classifier0 classifier1 ∧
        hsame ledger0 ledger1 ∧ hsame endpoint0 endpoint1

theorem RepresentationRingBHistRepresentationPacket_carrier_boundary [AskSetup] [PackageSetup]
    {group ring reps directSum tensor provenance classifier ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RepresentationRingBHistRepresentationPacket group ring reps directSum tensor provenance
        classifier ledger endpoint bundle pkg ->
      UnaryHistory group ∧ UnaryHistory ring ∧ UnaryHistory reps ∧ UnaryHistory directSum ∧
        UnaryHistory tensor ∧ UnaryHistory provenance ∧ UnaryHistory classifier ∧
          UnaryHistory ledger ∧ UnaryHistory endpoint ∧
            hsame ledger (append provenance classifier) ∧
              hsame endpoint (append ledger tensor) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have groupUnary : UnaryHistory group := packet.left
  have ringUnary : UnaryHistory ring := packet.right.left
  have repsUnary : UnaryHistory reps := packet.right.right.left
  have directSumUnary : UnaryHistory directSum := packet.right.right.right.left
  have tensorUnary : UnaryHistory tensor := packet.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance := packet.right.right.right.right.right.left
  have classifierUnary : UnaryHistory classifier :=
    packet.right.right.right.right.right.right.left
  have ledgerCont : Cont provenance classifier ledger :=
    packet.right.right.right.right.right.right.right.right.right.left
  have endpointCont : Cont ledger tensor endpoint :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed provenanceUnary classifierUnary ledgerCont
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledgerUnary tensorUnary endpointCont
  exact And.intro groupUnary
    (And.intro ringUnary
      (And.intro repsUnary
        (And.intro directSumUnary
          (And.intro tensorUnary
            (And.intro provenanceUnary
              (And.intro classifierUnary
                (And.intro ledgerUnary
                  (And.intro endpointUnary
                    (And.intro ledgerCont
                      (And.intro endpointCont
                        packet.right.right.right.right.right.right.right.right.right.right.right))))))))))

theorem RepresentationRingGrothendieckClassifier_transitive
    {group0 ring0 reps0 directSum0 tensor0 provenance0 classifier0 ledger0 endpoint0
      group1 ring1 reps1 directSum1 tensor1 provenance1 classifier1 ledger1 endpoint1
      group2 ring2 reps2 directSum2 tensor2 provenance2 classifier2 ledger2 endpoint2
      ledgerBridge01 ledgerBridge12 : BHist} :
    RepresentationRingGrothendieckClassifier group0 ring0 reps0 directSum0 tensor0
        provenance0 classifier0 ledger0 endpoint0 group1 ring1 reps1 directSum1 tensor1
        provenance1 classifier1 ledger1 endpoint1 ->
      RepresentationRingGrothendieckClassifier group1 ring1 reps1 directSum1 tensor1
          provenance1 classifier1 ledger1 endpoint1 group2 ring2 reps2 directSum2 tensor2
          provenance2 classifier2 ledger2 endpoint2 ->
        Cont ledger0 ledger1 ledgerBridge01 ->
          Cont ledger1 ledger2 ledgerBridge12 ->
            RepresentationRingGrothendieckClassifier group0 ring0 reps0 directSum0 tensor0
                provenance0 classifier0 ledger0 endpoint0 group2 ring2 reps2 directSum2 tensor2
                provenance2 classifier2 ledger2 endpoint2 ∧
              hsame ledgerBridge01 (append ledger0 ledger1) ∧
                hsame ledgerBridge12 (append ledger1 ledger2) := by
  intro left right bridge01 bridge12
  exact And.intro
    (And.intro (hsame_trans left.left right.left)
      (And.intro (hsame_trans left.right.left right.right.left)
        (And.intro (hsame_trans left.right.right.left right.right.right.left)
          (And.intro (hsame_trans left.right.right.right.left right.right.right.right.left)
            (And.intro
              (hsame_trans left.right.right.right.right.left
                right.right.right.right.right.left)
              (And.intro
                (hsame_trans left.right.right.right.right.right.left
                  right.right.right.right.right.right.left)
                (And.intro
                  (hsame_trans left.right.right.right.right.right.right.left
                    right.right.right.right.right.right.right.left)
                  (And.intro
                    (hsame_trans left.right.right.right.right.right.right.right.left
                      right.right.right.right.right.right.right.right.left)
                    (hsame_trans left.right.right.right.right.right.right.right.right
                      right.right.right.right.right.right.right.right.right)))))))))
    (And.intro bridge01 bridge12)

end BEDC.Derived.RepresentationRingUp
