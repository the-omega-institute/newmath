import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

namespace BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicCandidateNormalizationConfluenceRetainedPremiseInversion
    [AskSetup] [PackageSetup]
    {A K N F C D B T R P L endpointRead joinRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffCarrier A K N F C D B T R P L
        bundle pkg ->
      Cont K N endpointRead ->
        Cont F C joinRead ->
          PkgSig bundle joinRead pkg ->
            UnaryHistory K ∧ UnaryHistory F ∧ UnaryHistory C ∧ UnaryHistory D ∧
              UnaryHistory B ∧ UnaryHistory T ∧ UnaryHistory R ∧ UnaryHistory P ∧
                UnaryHistory L ∧ UnaryHistory endpointRead ∧ UnaryHistory joinRead ∧
                  Cont K N endpointRead ∧ Cont F C joinRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier endpointRoute joinRoute _joinPkg
  obtain ⟨_auditUnary, candidateUnary, endpointUnary, frontierUnary, residualUnary,
    decidableUnary, blockedUnary, transportUnary, replayUnary, provenanceUnary, localNameUnary,
    _provenancePkg⟩ := carrier
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed candidateUnary endpointUnary endpointRoute
  have joinReadUnary : UnaryHistory joinRead :=
    unary_cont_closed frontierUnary residualUnary joinRoute
  exact
    ⟨candidateUnary, frontierUnary, residualUnary, decidableUnary, blockedUnary,
      transportUnary, replayUnary, provenanceUnary, localNameUnary, endpointReadUnary,
      joinReadUnary, endpointRoute, joinRoute⟩

end BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp
