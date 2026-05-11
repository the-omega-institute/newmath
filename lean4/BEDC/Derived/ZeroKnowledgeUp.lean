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

end BEDC.Derived.ZeroKnowledgeUp
