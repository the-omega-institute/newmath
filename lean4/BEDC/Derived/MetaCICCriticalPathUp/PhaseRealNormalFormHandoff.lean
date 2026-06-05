import BEDC.Derived.MetaCICCriticalPathUp.Core

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPhaseRealNormalFormHandoff [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName normalRead streamSchedule regSeqReadback realSeal phaseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket transport
        route provenance localName bundle pkg →
      Cont strongNorm normalForm normalRead →
        Cont normalRead localName streamSchedule →
          Cont streamSchedule localName regSeqReadback →
            Cont regSeqReadback localName realSeal →
              Cont realSeal provenance phaseRead →
                PkgSig bundle phaseRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row phaseRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row normalRead ∨ hsame row streamSchedule ∨
                          hsame row regSeqReadback ∨ hsame row realSeal ∨
                            hsame row phaseRead ∨ hsame row obstruction ∨
                              hsame row dischargeSocket)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont strongNorm normalForm normalRead ∧
                          PkgSig bundle phaseRead pkg)
                      hsame ∧
                    UnaryHistory normalRead ∧ UnaryHistory phaseRead := by
  -- BEDC touchpoint anchor: MetaCICCriticalPathPacket BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro packet strongNormNormalFormNormal normalLocalSchedule scheduleLocalReadback
    readbackLocalSeal sealProvenancePhase phasePkg
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, _routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have normalUnary : UnaryHistory normalRead :=
    unary_cont_closed strongNormUnary normalFormUnary strongNormNormalFormNormal
  have scheduleUnary : UnaryHistory streamSchedule :=
    unary_cont_closed normalUnary localNameUnary normalLocalSchedule
  have readbackUnary : UnaryHistory regSeqReadback :=
    unary_cont_closed scheduleUnary localNameUnary scheduleLocalReadback
  have sealUnary : UnaryHistory realSeal :=
    unary_cont_closed readbackUnary localNameUnary readbackLocalSeal
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed sealUnary provenanceUnary sealProvenancePhase
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row phaseRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row normalRead ∨ hsame row streamSchedule ∨
              hsame row regSeqReadback ∨ hsame row realSeal ∨ hsame row phaseRead ∨
                hsame row obstruction ∨ hsame row dischargeSocket)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont strongNorm normalForm normalRead ∧
              PkgSig bundle phaseRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro phaseRead ⟨hsame_refl phaseRead, phaseUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, strongNormNormalFormNormal, phasePkg⟩
  }
  exact ⟨cert, normalUnary, phaseUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
