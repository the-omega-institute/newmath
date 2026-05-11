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

theorem ZeroKnowledgeCarrier_obligation [AskSetup] [PackageSetup]
    {prover verifier challenge response commitment computable simulator evidence dependency endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory prover -> UnaryHistory verifier -> UnaryHistory commitment ->
      UnaryHistory computable -> UnaryHistory simulator ->
        Cont prover verifier challenge -> Cont challenge prover response ->
          Cont response commitment evidence -> Cont simulator verifier dependency ->
            Cont evidence dependency endpoint -> PkgSig bundle endpoint pkg ->
              UnaryHistory challenge ∧ UnaryHistory response ∧ UnaryHistory evidence ∧
                UnaryHistory dependency ∧ UnaryHistory endpoint ∧
                  hsame challenge (append prover verifier) ∧
                    hsame response (append challenge prover) ∧
                      hsame evidence (append response commitment) ∧
                        hsame dependency (append simulator verifier) ∧
                          hsame endpoint (append evidence dependency) ∧
                            PkgSig bundle endpoint pkg := by
  intro proverUnary verifierUnary commitmentUnary computableUnary simulatorUnary
  intro challengeCont responseCont evidenceCont dependencyCont endpointCont packageSig
  have challengeUnary : UnaryHistory challenge :=
    unary_cont_closed proverUnary verifierUnary challengeCont
  have responseUnary : UnaryHistory response :=
    unary_cont_closed challengeUnary proverUnary responseCont
  have evidenceUnary : UnaryHistory evidence :=
    unary_cont_closed responseUnary commitmentUnary evidenceCont
  have dependencyUnary : UnaryHistory dependency :=
    unary_cont_closed simulatorUnary verifierUnary dependencyCont
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed evidenceUnary dependencyUnary endpointCont
  exact ⟨challengeUnary, responseUnary, evidenceUnary, dependencyUnary, endpointUnary,
    challengeCont, responseCont, evidenceCont, dependencyCont, endpointCont, packageSig⟩

def ZeroKnowledgeFinitePacket [AskSetup] [PackageSetup]
    (prover verifier challenge response commitment verifierRow simulator ledger endpoint : BHist)
    (hashBundle computableBundle : ProbeBundle ProbeName)
    (hashPkg computablePkg : Pkg) : Prop :=
  UnaryHistory prover ∧ UnaryHistory verifier ∧ UnaryHistory commitment ∧
    UnaryHistory verifierRow ∧ UnaryHistory simulator ∧
      Cont prover verifier challenge ∧ Cont challenge prover response ∧
        Cont response commitment verifierRow ∧ Cont simulator verifier ledger ∧
          Cont ledger verifierRow endpoint ∧ PkgSig hashBundle commitment hashPkg ∧
            PkgSig computableBundle verifierRow computablePkg

theorem ZeroKnowledgeFinitePacket_carrier_obligation [AskSetup] [PackageSetup]
    {prover verifier challenge response commitment verifierRow simulator ledger endpoint : BHist}
    {hashBundle computableBundle : ProbeBundle ProbeName} {hashPkg computablePkg : Pkg} :
    ZeroKnowledgeFinitePacket prover verifier challenge response commitment verifierRow simulator
        ledger endpoint hashBundle computableBundle hashPkg computablePkg ->
      UnaryHistory prover ∧ UnaryHistory verifier ∧ UnaryHistory challenge ∧
        UnaryHistory response ∧ UnaryHistory commitment ∧ UnaryHistory verifierRow ∧
          UnaryHistory simulator ∧ UnaryHistory ledger ∧ UnaryHistory endpoint ∧
            Cont prover verifier challenge ∧ Cont challenge prover response ∧
              Cont response commitment verifierRow ∧ Cont simulator verifier ledger ∧
                Cont ledger verifierRow endpoint ∧ PkgSig hashBundle commitment hashPkg ∧
                  PkgSig computableBundle verifierRow computablePkg := by
  intro packet
  obtain ⟨proverUnary, verifierUnary, commitmentUnary, verifierRowUnary, simulatorUnary,
    proverVerifierRow, challengeProverRow, responseCommitmentRow, simulatorVerifierRow,
    ledgerVerifierRow, hashSig, computableSig⟩ := packet
  have challengeUnary : UnaryHistory challenge :=
    unary_cont_closed proverUnary verifierUnary proverVerifierRow
  have responseUnary : UnaryHistory response :=
    unary_cont_closed challengeUnary proverUnary challengeProverRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed simulatorUnary verifierUnary simulatorVerifierRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledgerUnary verifierRowUnary ledgerVerifierRow
  exact And.intro proverUnary
    (And.intro verifierUnary
      (And.intro challengeUnary
        (And.intro responseUnary
          (And.intro commitmentUnary
            (And.intro verifierRowUnary
              (And.intro simulatorUnary
                (And.intro ledgerUnary
                  (And.intro endpointUnary
                    (And.intro proverVerifierRow
                      (And.intro challengeProverRow
                        (And.intro responseCommitmentRow
                          (And.intro simulatorVerifierRow
                            (And.intro ledgerVerifierRow
                              (And.intro hashSig computableSig))))))))))))))

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

theorem ZeroKnowledgeCarrier_simulation_ledger_obligation [AskSetup] [PackageSetup]
    {prover verifier challenge response commitment computableVerifier simulator ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZeroKnowledgeCarrier prover verifier challenge response commitment computableVerifier simulator
        ledger bundle pkg ->
      UnaryHistory simulator ∧ UnaryHistory verifier ∧ Cont simulator verifier ledger ∧
        Cont response commitment ledger ∧ hsame ledger (append simulator verifier) ∧
          hsame ledger (append response commitment) ∧ PkgSig bundle ledger pkg := by
  intro carrier
  have simulatorUnary : UnaryHistory simulator :=
    carrier.right.right.right.right.right.right.left
  have verifierUnary : UnaryHistory verifier :=
    carrier.right.left
  have responseCommitmentLedger : Cont response commitment ledger :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have simulatorVerifierLedger : Cont simulator verifier ledger :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have packageLedger : PkgSig bundle ledger pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right
  exact And.intro simulatorUnary
    (And.intro verifierUnary
      (And.intro simulatorVerifierLedger
        (And.intro responseCommitmentLedger
          (And.intro simulatorVerifierLedger
            (And.intro responseCommitmentLedger packageLedger)))))

theorem ZeroKnowledgeCarrier_soundness_ledger_obligation [AskSetup] [PackageSetup]
    {prover verifier challenge response commitment computableVerifier simulator ledger response'
      commitment' ledger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZeroKnowledgeCarrier prover verifier challenge response commitment computableVerifier simulator
        ledger bundle pkg ->
      hsame response response' ->
        hsame commitment commitment' ->
          Cont response' commitment' ledger' ->
            PkgSig bundle ledger' pkg ->
              ZeroKnowledgeCarrier prover verifier challenge response' commitment'
                    computableVerifier simulator ledger' bundle pkg ∧
                hsame ledger ledger' ∧ PkgSig bundle ledger' pkg := by
  intro carrier sameResponse sameCommitment targetLedger targetPkg
  have challengeRow : Cont prover verifier challenge :=
    carrier.right.right.right.right.right.right.right.right.left
  have responseRow : Cont challenge prover response :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have ledgerRow : Cont response commitment ledger :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have simulatorLedgerRow : Cont simulator verifier ledger :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameResponse sameCommitment ledgerRow targetLedger
  have _oldLedgerTransport : Cont response commitment ledger' :=
    cont_result_hsame_transport ledgerRow sameLedger
  have carrier' :
      ZeroKnowledgeCarrier prover verifier challenge response' commitment'
        computableVerifier simulator ledger' bundle pkg :=
    ⟨carrier.left,
      carrier.right.left,
      carrier.right.right.left,
      unary_transport carrier.right.right.right.left sameResponse,
      unary_transport carrier.right.right.right.right.left sameCommitment,
      carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.left,
      unary_transport carrier.right.right.right.right.right.right.right.left sameLedger,
      challengeRow,
      cont_result_hsame_transport responseRow sameResponse,
      targetLedger,
      cont_result_hsame_transport simulatorLedgerRow sameLedger,
      targetPkg⟩
  exact And.intro carrier' (And.intro sameLedger targetPkg)

def ZeroKnowledgeFiniteCarrier [AskSetup] [PackageSetup]
    (prover verifier challenge response commitment computable verifierAccept simulator ledger
      provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory prover ∧ UnaryHistory verifier ∧ UnaryHistory challenge ∧
    UnaryHistory response ∧ UnaryHistory commitment ∧ UnaryHistory computable ∧
      UnaryHistory verifierAccept ∧ UnaryHistory simulator ∧ UnaryHistory provenance ∧
        Cont prover verifier challenge ∧ Cont challenge prover response ∧
          Cont challenge computable verifierAccept ∧ Cont response verifierAccept ledger ∧
            Cont provenance ledger endpoint ∧ PkgSig bundle endpoint pkg

theorem ZeroKnowledgeFiniteCarrier_completeness_ledger_obligation [AskSetup] [PackageSetup]
    {prover verifier challenge response commitment computable verifierAccept simulator ledger
      provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZeroKnowledgeFiniteCarrier prover verifier challenge response commitment computable
        verifierAccept simulator ledger provenance endpoint bundle pkg ->
      UnaryHistory verifierAccept ∧ Cont challenge computable verifierAccept ∧
        Cont response verifierAccept ledger ∧ Cont provenance ledger endpoint ∧
          PkgSig bundle endpoint pkg := by
  intro carrier
  have verifierAcceptUnary : UnaryHistory verifierAccept :=
    carrier.right.right.right.right.right.right.left
  have verifierAcceptRow : Cont challenge computable verifierAccept :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have ledgerRow : Cont response verifierAccept ledger :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.left
  have endpointRow : Cont provenance ledger endpoint :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have packageRow : PkgSig bundle endpoint pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right
  exact And.intro verifierAcceptUnary
    (And.intro verifierAcceptRow
      (And.intro ledgerRow (And.intro endpointRow packageRow)))

end BEDC.Derived.ZeroKnowledgeUp
