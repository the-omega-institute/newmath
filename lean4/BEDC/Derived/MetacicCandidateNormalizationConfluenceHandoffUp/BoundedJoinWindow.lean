import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

namespace BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicCandidateNormalizationConfluenceHandoffBoundedJoinWindow
    [AskSetup] [PackageSetup]
    {audit candidate normalEndpoint frontier confluence decidability blocked transport replay
      provenance localName joinRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicCandidateNormalizationConfluenceHandoffCarrier audit candidate normalEndpoint frontier
        confluence decidability blocked transport replay provenance localName bundle pkg →
      Cont candidate frontier joinRead →
        PkgSig bundle joinRead pkg →
          UnaryHistory candidate ∧ UnaryHistory frontier ∧ UnaryHistory confluence ∧
            UnaryHistory decidability ∧ UnaryHistory blocked ∧ UnaryHistory transport ∧
              UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
                UnaryHistory joinRead ∧ Cont candidate frontier joinRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle joinRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier candidateFrontierRoute joinPkg
  obtain ⟨_auditUnary, candidateUnary, _normalEndpointUnary, frontierUnary, confluenceUnary,
    decidabilityUnary, blockedUnary, transportUnary, replayUnary, provenanceUnary, localNameUnary,
    provenancePkg⟩ := carrier
  have joinUnary : UnaryHistory joinRead :=
    unary_cont_closed candidateUnary frontierUnary candidateFrontierRoute
  exact
    ⟨candidateUnary, frontierUnary, confluenceUnary, decidabilityUnary, blockedUnary,
      transportUnary, replayUnary, provenanceUnary, localNameUnary, joinUnary,
      candidateFrontierRoute, provenancePkg, joinPkg⟩

end BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp
