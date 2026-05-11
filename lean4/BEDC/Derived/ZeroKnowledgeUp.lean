import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ZeroKnowledgeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ZeroKnowledgePacket [AskSetup] [PackageSetup]
    (prover verifier challenge response commitment computation simulator ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory prover ∧ UnaryHistory verifier ∧ UnaryHistory challenge ∧
    UnaryHistory response ∧ UnaryHistory commitment ∧ UnaryHistory computation ∧
      UnaryHistory simulator ∧ UnaryHistory ledger ∧ UnaryHistory endpoint ∧
        Cont prover verifier challenge ∧ Cont challenge prover response ∧
          Cont response commitment computation ∧ Cont simulator verifier ledger ∧
            Cont ledger computation endpoint ∧ PkgSig bundle endpoint pkg

theorem ZeroKnowledgePacket_classifier_transport [AskSetup] [PackageSetup]
    {prover verifier challenge response commitment computation simulator ledger endpoint prover'
      verifier' commitment' simulator' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZeroKnowledgePacket prover verifier challenge response commitment computation simulator ledger
      endpoint bundle pkg ->
      hsame prover prover' ->
        hsame verifier verifier' ->
          hsame commitment commitment' ->
            hsame simulator simulator' ->
              PkgSig bundle
                (append (append simulator' verifier')
                  (append (append (append prover' verifier') prover') commitment')) pkg ->
                exists challenge' : BHist,
                  exists response' : BHist,
                    exists computation' : BHist,
                      exists ledger' : BHist,
                        ZeroKnowledgePacket prover' verifier' challenge' response' commitment'
                            computation' simulator' ledger' (append ledger' computation')
                            bundle pkg ∧
                          hsame challenge challenge' ∧ hsame response response' ∧
                            hsame computation computation' ∧ hsame ledger ledger' := by
  intro packet sameProver sameVerifier sameCommitment sameSimulator pkgSig'
  let challenge' := append prover' verifier'
  let response' := append challenge' prover'
  let computation' := append response' commitment'
  let ledger' := append simulator' verifier'
  have challengeCont' : Cont prover' verifier' challenge' := rfl
  have responseCont' : Cont challenge' prover' response' := rfl
  have computationCont' : Cont response' commitment' computation' := rfl
  have ledgerCont' : Cont simulator' verifier' ledger' := rfl
  have endpointCont' : Cont ledger' computation' (append ledger' computation') := rfl
  have sameChallenge : hsame challenge challenge' :=
    cont_respects_hsame sameProver sameVerifier
      packet.right.right.right.right.right.right.right.right.right.left challengeCont'
  have sameResponse : hsame response response' :=
    cont_respects_hsame sameChallenge sameProver
      packet.right.right.right.right.right.right.right.right.right.right.left responseCont'
  have sameComputation : hsame computation computation' :=
    cont_respects_hsame sameResponse sameCommitment
      packet.right.right.right.right.right.right.right.right.right.right.right.left
      computationCont'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameSimulator sameVerifier
      packet.right.right.right.right.right.right.right.right.right.right.right.right.left
      ledgerCont'
  have proverUnary' : UnaryHistory prover' :=
    unary_transport packet.left sameProver
  have verifierUnary' : UnaryHistory verifier' :=
    unary_transport packet.right.left sameVerifier
  have challengeUnary' : UnaryHistory challenge' :=
    unary_cont_closed proverUnary' verifierUnary' challengeCont'
  have responseUnary' : UnaryHistory response' :=
    unary_cont_closed challengeUnary' proverUnary' responseCont'
  have commitmentUnary' : UnaryHistory commitment' :=
    unary_transport packet.right.right.right.right.left sameCommitment
  have computationUnary' : UnaryHistory computation' :=
    unary_cont_closed responseUnary' commitmentUnary' computationCont'
  have simulatorUnary' : UnaryHistory simulator' :=
    unary_transport packet.right.right.right.right.right.right.left sameSimulator
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed simulatorUnary' verifierUnary' ledgerCont'
  have endpointUnary' : UnaryHistory (append ledger' computation') :=
    unary_cont_closed ledgerUnary' computationUnary' endpointCont'
  refine ⟨challenge', response', computation', ledger', ?_⟩
  constructor
  · exact
      And.intro proverUnary'
        (And.intro verifierUnary'
          (And.intro challengeUnary'
            (And.intro responseUnary'
              (And.intro commitmentUnary'
                (And.intro computationUnary'
                  (And.intro simulatorUnary'
                    (And.intro ledgerUnary'
                      (And.intro endpointUnary'
                        (And.intro challengeCont'
                          (And.intro responseCont'
                            (And.intro computationCont'
                              (And.intro ledgerCont'
                                (And.intro endpointCont' pkgSig')))))))))))))
  · exact And.intro sameChallenge
      (And.intro sameResponse (And.intro sameComputation sameLedger))

end BEDC.Derived.ZeroKnowledgeUp
