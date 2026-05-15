import BEDC.Derived.MetaCICNormalizationFrontierUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetaCICNormalizationFrontierCarrier [AskSetup] [PackageSetup]
    (candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory candidate ∧ UnaryHistory closedCandidate ∧ UnaryHistory finished ∧
    UnaryHistory endpoint ∧ UnaryHistory obstruction ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localRow ∧
        Cont candidate closedCandidate localRow ∧ Cont finished endpoint replay ∧
          Cont endpoint replay provenance ∧ hsame transport (append candidate finished) ∧
            PkgSig bundle provenance pkg

theorem MetaCICNormalizationFrontierCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead finishedRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint finishedRead ->
          Cont endpoint replay endpointRead ->
            PkgSig bundle endpointRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished
                      endpoint obstruction transport replay provenance localRow bundle pkg ∧
                      hsame row localRow)
                  (fun row : BHist => hsame row localRow ∧ UnaryHistory row)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle endpointRead pkg ∧
                      hsame row localRow)
                  hsame ∧
                UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧
                  UnaryHistory endpointRead ∧ Cont candidate closedCandidate candidateRead ∧
                    Cont finished endpoint finishedRead ∧ Cont endpoint replay endpointRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier candidateClosedRead finishedEndpointRead endpointReplayRead endpointReadPkg
  have carrierPacket :
      MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg :=
    carrier
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    _obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed endpointUnary replayUnary endpointReplayRead
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            MetaCICNormalizationFrontierCarrier candidate closedCandidate finished
              endpoint obstruction transport replay provenance localRow bundle pkg ∧
              hsame row localRow)
          (fun row : BHist => hsame row localRow ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle endpointRead pkg ∧
              hsame row localRow)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro localRow ⟨carrierPacket, hsame_refl localRow⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.right, unary_transport localRowUnary (hsame_symm source.right)⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, endpointReadPkg, source.right⟩
    }
  exact
    ⟨cert, candidateReadUnary, finishedReadUnary, endpointReadUnary, candidateClosedRead,
      finishedEndpointRead, endpointReplayRead, provenancePkg, endpointReadPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
