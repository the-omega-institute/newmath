import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathResidualDiamondCandidateMediatedHandoff
    [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName residualRead diamondRead candidateRead l10Read : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route transport residualRead →
        Cont residualRead dischargeSocket diamondRead →
          Cont diamondRead strongNorm candidateRead →
            Cont candidateRead handoff l10Read →
              PkgSig bundle l10Read pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row l10Read ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row residualRead ∨ hsame row diamondRead ∨
                        hsame row candidateRead ∨ hsame row l10Read ∨ hsame row provenance)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont route transport residualRead ∧
                        Cont residualRead dischargeSocket diamondRead ∧
                          Cont diamondRead strongNorm candidateRead ∧
                            Cont candidateRead handoff l10Read ∧ PkgSig bundle l10Read pkg)
                    hsame ∧
                  UnaryHistory residualRead ∧ UnaryHistory diamondRead ∧
                    UnaryHistory candidateRead ∧ UnaryHistory l10Read := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet routeTransportResidual residualSocketDiamond diamondStrongCandidate
    candidateHandoffL10 l10Pkg
  obtain ⟨strongNormUnary, _normalFormUnary, _obstructionUnary, handoffUnary,
    dischargeSocketUnary, transportUnary, routeUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed routeUnary transportUnary routeTransportResidual
  have diamondUnary : UnaryHistory diamondRead :=
    unary_cont_closed residualUnary dischargeSocketUnary residualSocketDiamond
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed diamondUnary strongNormUnary diamondStrongCandidate
  have l10Unary : UnaryHistory l10Read :=
    unary_cont_closed candidateUnary handoffUnary candidateHandoffL10
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row l10Read ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row residualRead ∨ hsame row diamondRead ∨ hsame row candidateRead ∨
              hsame row l10Read ∨ hsame row provenance)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont route transport residualRead ∧
              Cont residualRead dischargeSocket diamondRead ∧
                Cont diamondRead strongNorm candidateRead ∧
                  Cont candidateRead handoff l10Read ∧ PkgSig bundle l10Read pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro l10Read ⟨hsame_refl l10Read, l10Unary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeTransportResidual, residualSocketDiamond, diamondStrongCandidate,
          candidateHandoffL10, l10Pkg⟩
  }
  exact ⟨cert, residualUnary, diamondUnary, candidateUnary, l10Unary⟩

end BEDC.Derived.MetaCICCriticalPathUp
