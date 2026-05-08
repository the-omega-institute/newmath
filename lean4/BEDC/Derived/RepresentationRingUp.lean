import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RepresentationRingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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
theorem RepresentationRingBHistRepresentationPacket_direct_sum_tensor_ledger_stability
    [AskSetup] [PackageSetup]
    {group ring reps directSum directSumPrime tensor tensorPrime provenance classifier
      classifierPrime ledger ledgerPrime endpoint endpointPrime : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RepresentationRingBHistRepresentationPacket group ring reps directSum tensor provenance
        classifier ledger endpoint bundle pkg ->
      hsame directSum directSumPrime ->
        hsame tensor tensorPrime ->
          hsame classifier classifierPrime ->
            Cont reps directSumPrime tensorPrime ->
              Cont provenance classifierPrime ledgerPrime ->
                Cont ledgerPrime tensorPrime endpointPrime ->
                  PkgSig bundle endpointPrime pkg ->
                    RepresentationRingBHistRepresentationPacket group ring reps directSumPrime
                        tensorPrime provenance classifierPrime ledgerPrime endpointPrime bundle pkg ∧
                      hsame ledger ledgerPrime ∧ hsame endpoint endpointPrime := by
  intro packet sameDirectSum sameTensor sameClassifier repsRow' ledgerRow' endpointRow' pkgSig'
  have directSumUnary' : UnaryHistory directSumPrime :=
    unary_transport packet.right.right.right.left sameDirectSum
  have tensorUnary' : UnaryHistory tensorPrime :=
    unary_transport packet.right.right.right.right.left sameTensor
  have classifierUnary' : UnaryHistory classifierPrime :=
    unary_transport packet.right.right.right.right.right.right.left sameClassifier
  have ledgerUnary' : UnaryHistory ledgerPrime :=
    unary_cont_closed packet.right.right.right.right.right.left classifierUnary' ledgerRow'
  have endpointUnary' : UnaryHistory endpointPrime :=
    unary_cont_closed ledgerUnary' tensorUnary' endpointRow'
  have sameLedger : hsame ledger ledgerPrime :=
    cont_respects_hsame (hsame_refl provenance) sameClassifier
      packet.right.right.right.right.right.right.right.right.right.left ledgerRow'
  have sameEndpoint : hsame endpoint endpointPrime :=
    cont_respects_hsame sameLedger sameTensor
      packet.right.right.right.right.right.right.right.right.right.right.left endpointRow'
  have packet' :
      RepresentationRingBHistRepresentationPacket group ring reps directSumPrime tensorPrime
        provenance classifierPrime ledgerPrime endpointPrime bundle pkg :=
    And.intro packet.left
      (And.intro packet.right.left
        (And.intro packet.right.right.left
          (And.intro directSumUnary'
            (And.intro tensorUnary'
              (And.intro packet.right.right.right.right.right.left
                (And.intro classifierUnary'
                  (And.intro repsRow'
                    (And.intro packet.right.right.right.right.right.right.right.right.left
                      (And.intro ledgerRow'
                        (And.intro endpointRow' pkgSig'))))))))))
  exact And.intro packet' (And.intro sameLedger sameEndpoint)

theorem RepresentationRingBHistRepresentationPacket_grothendieck_classifier_symmetric
    [AskSetup] [PackageSetup]
    {group ring reps directSum tensor provenance classifier ledger endpoint group' ring' reps'
      directSum' tensor' provenance' classifier' ledger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RepresentationRingBHistRepresentationPacket group ring reps directSum tensor provenance
        classifier ledger endpoint bundle pkg ->
      RepresentationRingBHistRepresentationPacket group' ring' reps' directSum' tensor'
        provenance' classifier' ledger' endpoint' bundle pkg ->
        RepresentationRingGrothendieckClassifier group ring reps directSum tensor provenance
          classifier ledger endpoint group' ring' reps' directSum' tensor' provenance'
          classifier' ledger' endpoint' ->
          RepresentationRingGrothendieckClassifier group' ring' reps' directSum' tensor'
            provenance' classifier' ledger' endpoint' group ring reps directSum tensor
            provenance classifier ledger endpoint := by
  intro _packet _packet' classified
  exact And.intro (hsame_symm classified.left)
    (And.intro (hsame_symm classified.right.left)
      (And.intro (hsame_symm classified.right.right.left)
        (And.intro (hsame_symm classified.right.right.right.left)
          (And.intro (hsame_symm classified.right.right.right.right.left)
            (And.intro (hsame_symm classified.right.right.right.right.right.left)
              (And.intro (hsame_symm classified.right.right.right.right.right.right.left)
                (And.intro (hsame_symm classified.right.right.right.right.right.right.right.left)
                  (hsame_symm classified.right.right.right.right.right.right.right.right))))))))

theorem RepresentationRingBHistRepresentationPacket_semantic_name_certificate [AskSetup]
    [PackageSetup]
    {group ring reps directSum tensor provenance classifier ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RepresentationRingBHistRepresentationPacket group ring reps directSum tensor provenance
        classifier ledger endpoint bundle pkg ->
      SemanticNameCert
        (fun target : BHist =>
          exists carriedLedger : BHist,
            RepresentationRingBHistRepresentationPacket group ring reps directSum tensor provenance
              classifier carriedLedger target bundle pkg)
        (fun target : BHist =>
          exists carriedLedger : BHist,
            RepresentationRingBHistRepresentationPacket group ring reps directSum tensor provenance
              classifier carriedLedger target bundle pkg)
        (fun target : BHist =>
          exists carriedLedger : BHist,
            RepresentationRingBHistRepresentationPacket group ring reps directSum tensor provenance
              classifier carriedLedger target bundle pkg)
        (fun left right : BHist =>
          (exists leftLedger : BHist,
            RepresentationRingBHistRepresentationPacket group ring reps directSum tensor provenance
              classifier leftLedger left bundle pkg) ∧
            (exists rightLedger : BHist,
              RepresentationRingBHistRepresentationPacket group ring reps directSum tensor provenance
                classifier rightLedger right bundle pkg) ∧
              hsame left right) := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint (Exists.intro ledger packet)
      equiv_refl := by
        intro target source
        exact And.intro source (And.intro source (hsame_refl target))
      equiv_symm := by
        intro _left _right classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro _left _middle _right classifiedLeft classifiedRight
        exact And.intro classifiedLeft.left
          (And.intro classifiedRight.right.left
            (hsame_trans classifiedLeft.right.right classifiedRight.right.right))
      carrier_respects_equiv := by
        intro _left _right classified _source
        exact classified.right.left
    }
    pattern_sound := by
      intro _target source
      exact source
    ledger_sound := by
      intro _target source
      exact source
  }

end BEDC.Derived.RepresentationRingUp
