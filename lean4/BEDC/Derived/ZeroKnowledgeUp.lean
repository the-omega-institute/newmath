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

def ZeroKnowledgeCarrier [AskSetup] [PackageSetup]
    (prover verifier challenge response commitment computableVerifier simulator ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory prover ∧ UnaryHistory verifier ∧ UnaryHistory challenge ∧
    UnaryHistory response ∧ UnaryHistory commitment ∧ UnaryHistory computableVerifier ∧
      UnaryHistory simulator ∧ UnaryHistory ledger ∧ Cont prover verifier challenge ∧
        Cont challenge prover response ∧ Cont response commitment ledger ∧
          Cont simulator verifier ledger ∧ PkgSig bundle ledger pkg

theorem ZeroKnowledgeCarrier_classifier_obligation [AskSetup] [PackageSetup]
    {prover verifier challenge response commitment computableVerifier simulator ledger prover'
      verifier' challenge' response' commitment' computableVerifier' simulator' ledger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZeroKnowledgeCarrier prover verifier challenge response commitment computableVerifier simulator
        ledger bundle pkg ->
      hsame prover prover' ->
        hsame verifier verifier' ->
          hsame commitment commitment' ->
            hsame computableVerifier computableVerifier' ->
              hsame simulator simulator' ->
                Cont prover' verifier' challenge' ->
                  Cont challenge' prover' response' ->
                    Cont response' commitment' ledger' ->
                      Cont simulator' verifier' ledger' ->
                        PkgSig bundle ledger' pkg ->
                          ZeroKnowledgeCarrier prover' verifier' challenge' response' commitment'
                              computableVerifier' simulator' ledger' bundle pkg ∧
                            hsame challenge challenge' ∧ hsame response response' ∧
                              hsame ledger ledger' := by
  intro carrier sameProver sameVerifier sameCommitment sameComputable sameSimulator
  intro targetChallenge targetResponse targetLedger targetSimulatorLedger targetPkg
  have sameChallenge : hsame challenge challenge' :=
    cont_respects_hsame sameProver sameVerifier
      carrier.right.right.right.right.right.right.right.right.left targetChallenge
  have sameResponse : hsame response response' :=
    cont_respects_hsame sameChallenge sameProver
      carrier.right.right.right.right.right.right.right.right.right.left targetResponse
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameResponse sameCommitment
      carrier.right.right.right.right.right.right.right.right.right.right.left targetLedger
  have carrier' :
      ZeroKnowledgeCarrier prover' verifier' challenge' response' commitment'
        computableVerifier' simulator' ledger' bundle pkg :=
    ⟨unary_transport carrier.left sameProver,
      unary_transport carrier.right.left sameVerifier,
      unary_transport carrier.right.right.left sameChallenge,
      unary_transport carrier.right.right.right.left sameResponse,
      unary_transport carrier.right.right.right.right.left sameCommitment,
      unary_transport carrier.right.right.right.right.right.left sameComputable,
      unary_transport carrier.right.right.right.right.right.right.left sameSimulator,
      unary_transport carrier.right.right.right.right.right.right.right.left sameLedger,
      targetChallenge,
      targetResponse,
      targetLedger,
      targetSimulatorLedger,
      targetPkg⟩
  exact ⟨carrier', sameChallenge, sameResponse, sameLedger⟩

end BEDC.Derived.ZeroKnowledgeUp
