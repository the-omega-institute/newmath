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

def ZeroKnowledgeFiniteCarrier [AskSetup] [PackageSetup]
    (prover verifier challenge response commitment verifierComp simulator ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory prover ∧ UnaryHistory verifier ∧ UnaryHistory challenge ∧
    UnaryHistory response ∧ UnaryHistory commitment ∧ UnaryHistory verifierComp ∧
      UnaryHistory simulator ∧ UnaryHistory ledger ∧ UnaryHistory endpoint ∧
        Cont prover verifier challenge ∧ Cont challenge prover response ∧
          Cont response commitment ledger ∧ Cont simulator verifier endpoint ∧
            PkgSig bundle endpoint pkg

theorem ZeroKnowledgeFiniteCarrier_classifier_obligation [AskSetup] [PackageSetup]
    {prover verifier challenge response commitment verifierComp simulator ledger endpoint
      prover' verifier' commitment' verifierComp' simulator' challenge' response' ledger'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZeroKnowledgeFiniteCarrier prover verifier challenge response commitment verifierComp simulator
      ledger endpoint bundle pkg ->
    hsame prover prover' ->
    hsame verifier verifier' ->
    hsame commitment commitment' ->
    hsame verifierComp verifierComp' ->
    hsame simulator simulator' ->
    Cont prover' verifier' challenge' ->
    Cont challenge' prover' response' ->
    Cont response' commitment' ledger' ->
    Cont simulator' verifier' endpoint' ->
    PkgSig bundle endpoint' pkg ->
    ZeroKnowledgeFiniteCarrier prover' verifier' challenge' response' commitment'
        verifierComp' simulator' ledger' endpoint' bundle pkg ∧
      hsame challenge challenge' ∧ hsame response response' ∧ hsame ledger ledger' ∧
        hsame endpoint endpoint' := by
  intro carrier sameProver sameVerifier sameCommitment sameVerifierComp sameSimulator
  intro challengeRow' responseRow' ledgerRow' endpointRow' pkgSig'
  have proverUnary : UnaryHistory prover := carrier.left
  have verifierUnary : UnaryHistory verifier := carrier.right.left
  have challengeUnary : UnaryHistory challenge := carrier.right.right.left
  have responseUnary : UnaryHistory response := carrier.right.right.right.left
  have commitmentUnary : UnaryHistory commitment := carrier.right.right.right.right.left
  have verifierCompUnary : UnaryHistory verifierComp :=
    carrier.right.right.right.right.right.left
  have simulatorUnary : UnaryHistory simulator :=
    carrier.right.right.right.right.right.right.left
  have proverUnary' : UnaryHistory prover' := unary_transport proverUnary sameProver
  have verifierUnary' : UnaryHistory verifier' := unary_transport verifierUnary sameVerifier
  have commitmentUnary' : UnaryHistory commitment' :=
    unary_transport commitmentUnary sameCommitment
  have verifierCompUnary' : UnaryHistory verifierComp' :=
    unary_transport verifierCompUnary sameVerifierComp
  have simulatorUnary' : UnaryHistory simulator' := unary_transport simulatorUnary sameSimulator
  have challengeUnary' : UnaryHistory challenge' :=
    unary_cont_closed proverUnary' verifierUnary' challengeRow'
  have responseUnary' : UnaryHistory response' :=
    unary_cont_closed challengeUnary' proverUnary' responseRow'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed responseUnary' commitmentUnary' ledgerRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed simulatorUnary' verifierUnary' endpointRow'
  have challengeSame : hsame challenge challenge' :=
    cont_respects_hsame sameProver sameVerifier
      carrier.right.right.right.right.right.right.right.right.right.left challengeRow'
  have responseSame : hsame response response' :=
    cont_respects_hsame challengeSame sameProver
      carrier.right.right.right.right.right.right.right.right.right.right.left responseRow'
  have ledgerSame : hsame ledger ledger' :=
    cont_respects_hsame responseSame sameCommitment
      carrier.right.right.right.right.right.right.right.right.right.right.right.left
      ledgerRow'
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame sameSimulator sameVerifier
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.left
      endpointRow'
  constructor
  · constructor
    · exact proverUnary'
    · constructor
      · exact verifierUnary'
      · constructor
        · exact challengeUnary'
        · constructor
          · exact responseUnary'
          · constructor
            · exact commitmentUnary'
            · constructor
              · exact verifierCompUnary'
              · constructor
                · exact simulatorUnary'
                · constructor
                  · exact ledgerUnary'
                  · constructor
                    · exact endpointUnary'
                    · constructor
                      · exact challengeRow'
                      · constructor
                        · exact responseRow'
                        · constructor
                          · exact ledgerRow'
                          · constructor
                            · exact endpointRow'
                            · exact pkgSig'
  · constructor
    · exact challengeSame
    · constructor
      · exact responseSame
      · constructor
        · exact ledgerSame
        · exact endpointSame

end BEDC.Derived.ZeroKnowledgeUp
