import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPublicInterfaceFrontierReadiness [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName candidateSN confluenceFrontier finiteObservation normalizationFrontier
      subjectReductionSocket frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket transport
        route provenance localName bundle pkg →
      Cont route provenance candidateSN →
        Cont candidateSN handoff confluenceFrontier →
          Cont confluenceFrontier dischargeSocket finiteObservation →
            Cont finiteObservation normalForm normalizationFrontier →
              Cont normalizationFrontier obstruction subjectReductionSocket →
                Cont subjectReductionSocket localName frontierRead →
                  PkgSig bundle frontierRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row candidateSN ∨ hsame row confluenceFrontier ∨
                            hsame row finiteObservation ∨ hsame row normalizationFrontier ∨
                              hsame row subjectReductionSocket ∨ hsame row frontierRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle frontierRead pkg ∧
                            PkgSig bundle provenance pkg ∧
                              Cont normalizationFrontier obstruction subjectReductionSocket)
                        hsame ∧
                      UnaryHistory frontierRead := by
  -- BEDC touchpoint anchor: MetaCICCriticalPathPacket BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro packet routeProvenanceCandidate candidateHandoffConfluence
    confluenceDischargeFinite finiteNormalNormalization normalizationObstructionSubject
    subjectLocalFrontier frontierPkg
  obtain ⟨_strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateSN :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceCandidate
  have confluenceUnary : UnaryHistory confluenceFrontier :=
    unary_cont_closed candidateUnary handoffUnary candidateHandoffConfluence
  have finiteUnary : UnaryHistory finiteObservation :=
    unary_cont_closed confluenceUnary dischargeSocketUnary confluenceDischargeFinite
  have normalizationUnary : UnaryHistory normalizationFrontier :=
    unary_cont_closed finiteUnary normalFormUnary finiteNormalNormalization
  have subjectUnary : UnaryHistory subjectReductionSocket :=
    unary_cont_closed normalizationUnary obstructionUnary normalizationObstructionSubject
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed subjectUnary localNameUnary subjectLocalFrontier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateSN ∨ hsame row confluenceFrontier ∨
              hsame row finiteObservation ∨ hsame row normalizationFrontier ∨
                hsame row subjectReductionSocket ∨ hsame row frontierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle frontierRead pkg ∧
              PkgSig bundle provenance pkg ∧
                Cont normalizationFrontier obstruction subjectReductionSocket)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro frontierRead ⟨hsame_refl frontierRead, frontierUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, frontierPkg, provenancePkg, normalizationObstructionSubject⟩
  }
  exact ⟨cert, frontierUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
