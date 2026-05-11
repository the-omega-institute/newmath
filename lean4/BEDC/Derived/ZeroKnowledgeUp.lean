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

end BEDC.Derived.ZeroKnowledgeUp
