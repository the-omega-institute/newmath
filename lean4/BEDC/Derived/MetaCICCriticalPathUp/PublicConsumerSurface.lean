import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPublicConsumerSurface [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName candidateSN confluenceFrontier finiteObservation normalizationFrontier
      subjectReductionSocket consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route provenance candidateSN →
        Cont candidateSN handoff confluenceFrontier →
          Cont confluenceFrontier dischargeSocket finiteObservation →
            Cont finiteObservation normalForm normalizationFrontier →
              Cont normalizationFrontier obstruction subjectReductionSocket →
                Cont subjectReductionSocket localName consumerRead →
                  PkgSig bundle consumerRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row candidateSN ∨ hsame row confluenceFrontier ∨
                            hsame row finiteObservation ∨ hsame row normalizationFrontier ∨
                              hsame row subjectReductionSocket ∨ hsame row consumerRead)
                        (fun row : BHist =>
                          hsame row consumerRead ∧ PkgSig bundle consumerRead pkg ∧
                            PkgSig bundle provenance pkg)
                        hsame ∧
                      UnaryHistory consumerRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeProvenanceCandidate candidateHandoffConfluence
    confluenceSocketFinite finiteNormalFrontier frontierObstructionSubject
    subjectLocalConsumer consumerPkg
  obtain ⟨_strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateSN :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceCandidate
  have confluenceUnary : UnaryHistory confluenceFrontier :=
    unary_cont_closed candidateUnary handoffUnary candidateHandoffConfluence
  have finiteUnary : UnaryHistory finiteObservation :=
    unary_cont_closed confluenceUnary dischargeSocketUnary confluenceSocketFinite
  have normalizationUnary : UnaryHistory normalizationFrontier :=
    unary_cont_closed finiteUnary normalFormUnary finiteNormalFrontier
  have subjectUnary : UnaryHistory subjectReductionSocket :=
    unary_cont_closed normalizationUnary obstructionUnary frontierObstructionSubject
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed subjectUnary localNameUnary subjectLocalConsumer
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateSN ∨ hsame row confluenceFrontier ∨
              hsame row finiteObservation ∨ hsame row normalizationFrontier ∨
                hsame row subjectReductionSocket ∨ hsame row consumerRead)
          (fun row : BHist =>
            hsame row consumerRead ∧ PkgSig bundle consumerRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
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
      exact ⟨source.left, consumerPkg, provenancePkg⟩
  }
  exact ⟨cert, consumerUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
