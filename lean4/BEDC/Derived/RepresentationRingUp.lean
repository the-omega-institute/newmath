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

theorem RepresentationRingBHistRepresentationPacket_grothendieck_classifier_transitive
    [AskSetup] [PackageSetup]
    {group0 ring0 reps0 directSum0 tensor0 provenance0 classifier0 ledger0 endpoint0 group1
      ring1 reps1 directSum1 tensor1 provenance1 classifier1 ledger1 endpoint1 group2 ring2 reps2
      directSum2 tensor2 provenance2 classifier2 ledger2 endpoint2 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RepresentationRingBHistRepresentationPacket group0 ring0 reps0 directSum0 tensor0 provenance0
        classifier0 ledger0 endpoint0 bundle pkg ->
      RepresentationRingBHistRepresentationPacket group1 ring1 reps1 directSum1 tensor1
          provenance1 classifier1 ledger1 endpoint1 bundle pkg ->
        RepresentationRingBHistRepresentationPacket group2 ring2 reps2 directSum2 tensor2
            provenance2 classifier2 ledger2 endpoint2 bundle pkg ->
          hsame group0 group1 ->
            hsame group1 group2 ->
              hsame ring0 ring1 ->
                hsame ring1 ring2 ->
                  hsame reps0 reps1 ->
                    hsame reps1 reps2 ->
                      hsame directSum0 directSum1 ->
                        hsame directSum1 directSum2 ->
                          hsame tensor0 tensor1 ->
                            hsame tensor1 tensor2 ->
                              hsame provenance0 provenance1 ->
                                hsame provenance1 provenance2 ->
                                  hsame classifier0 classifier1 ->
                                    hsame classifier1 classifier2 ->
                                      hsame ledger0 ledger1 ->
                                        hsame ledger1 ledger2 ->
                                          hsame endpoint0 endpoint1 ->
                                            hsame endpoint1 endpoint2 ->
                                              hsame group0 group2 ∧ hsame ring0 ring2 ∧
                                                hsame reps0 reps2 ∧
                                                  hsame directSum0 directSum2 ∧
                                                    hsame tensor0 tensor2 ∧
                                                      hsame provenance0 provenance2 ∧
                                                        hsame classifier0 classifier2 ∧
                                                          hsame ledger0 ledger2 ∧
                                                            hsame endpoint0 endpoint2 := by
  intro packet0 packet1 packet2 sameGroup01 sameGroup12 sameRing01 sameRing12 sameReps01
    sameReps12 sameDirectSum01 sameDirectSum12 sameTensor01 sameTensor12 sameProvenance01
    sameProvenance12 sameClassifier01 sameClassifier12 sameLedger01 sameLedger12 sameEndpoint01
    sameEndpoint12
  have _boundary0 :=
    RepresentationRingBHistRepresentationPacket_carrier_boundary packet0
  have _boundary1 :=
    RepresentationRingBHistRepresentationPacket_carrier_boundary packet1
  have _boundary2 :=
    RepresentationRingBHistRepresentationPacket_carrier_boundary packet2
  exact And.intro (hsame_trans sameGroup01 sameGroup12)
    (And.intro (hsame_trans sameRing01 sameRing12)
      (And.intro (hsame_trans sameReps01 sameReps12)
        (And.intro (hsame_trans sameDirectSum01 sameDirectSum12)
          (And.intro (hsame_trans sameTensor01 sameTensor12)
            (And.intro (hsame_trans sameProvenance01 sameProvenance12)
              (And.intro (hsame_trans sameClassifier01 sameClassifier12)
                (And.intro (hsame_trans sameLedger01 sameLedger12)
                  (hsame_trans sameEndpoint01 sameEndpoint12))))))))

end BEDC.Derived.RepresentationRingUp
