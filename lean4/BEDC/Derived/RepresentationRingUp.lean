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

def RepresentationRingGrothendieckClassifier
    (group ring reps directSum tensor provenance classifier ledger group' ring' reps' directSum'
      tensor' provenance' classifier' ledger' : BHist) : Prop :=
  hsame group group' ∧ hsame ring ring' ∧ hsame reps reps' ∧ hsame directSum directSum' ∧
    hsame tensor tensor' ∧ hsame provenance provenance' ∧ hsame classifier classifier' ∧
      hsame ledger ledger'

theorem RepresentationRingGrothendieckClassifier_symmetric
    {group ring reps directSum tensor provenance classifier ledger group' ring' reps' directSum'
      tensor' provenance' classifier' ledger' : BHist} :
    RepresentationRingGrothendieckClassifier group ring reps directSum tensor provenance classifier
        ledger group' ring' reps' directSum' tensor' provenance' classifier' ledger' ->
      RepresentationRingGrothendieckClassifier group' ring' reps' directSum' tensor' provenance'
          classifier' ledger' group ring reps directSum tensor provenance classifier ledger ∧
        hsame ledger' ledger := by
  intro classified
  have ledgerSame : hsame ledger' ledger :=
    hsame_symm classified.right.right.right.right.right.right.right
  exact And.intro
    (And.intro (hsame_symm classified.left)
      (And.intro (hsame_symm classified.right.left)
        (And.intro (hsame_symm classified.right.right.left)
          (And.intro (hsame_symm classified.right.right.right.left)
            (And.intro (hsame_symm classified.right.right.right.right.left)
              (And.intro (hsame_symm classified.right.right.right.right.right.left)
                (And.intro (hsame_symm classified.right.right.right.right.right.right.left)
                  ledgerSame)))))))
    ledgerSame

end BEDC.Derived.RepresentationRingUp
