import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierNonescape [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance localRow
      candidateRead finishedRead endpointRead frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint finishedRead ->
          Cont endpoint replay endpointRead ->
            Cont endpointRead localRow frontierRead ->
              PkgSig bundle frontierRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row candidateRead ∨ hsame row finishedRead ∨
                        hsame row endpointRead ∨ hsame row obstruction ∨
                          hsame row frontierRead)
                    (fun row : BHist =>
                      PkgSig bundle frontierRead pkg ∧ hsame row frontierRead)
                    hsame ∧
                  UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧
                    UnaryHistory endpointRead ∧ UnaryHistory frontierRead ∧
                      hsame obstruction obstruction := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier candidateClosedRead finishedEndpointRead endpointReplayRead
    frontierRoute frontierPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed endpointUnary replayUnary endpointReplayRead
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed endpointReadUnary localRowUnary frontierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row finishedRead ∨ hsame row endpointRead ∨
              hsame row obstruction ∨ hsame row frontierRead)
          (fun row : BHist => PkgSig bundle frontierRead pkg ∧ hsame row frontierRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro frontierRead ⟨hsame_refl frontierRead, frontierReadUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨frontierPkg, source.left⟩
    }
  exact
    ⟨cert, candidateReadUnary, finishedReadUnary, endpointReadUnary, frontierReadUnary,
      hsame_refl obstruction⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
