import BEDC.Derived.MetaCICCriticalPathUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPhaseRealAuditCleanFloor [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadicFace streamFace regSeqRatFace realFace auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName dyadicFace →
        Cont dyadicFace provenance streamFace →
          Cont streamFace normalForm regSeqRatFace →
            Cont regSeqRatFace transport realFace →
              Cont realFace localName auditRead →
                PkgSig bundle auditRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row dyadicFace ∨ hsame row streamFace ∨
                          hsame row regSeqRatFace ∨ hsame row realFace ∨
                            hsame row auditRead)
                      (fun row : BHist =>
                        hsame row auditRead ∧ PkgSig bundle auditRead pkg ∧
                          PkgSig bundle provenance pkg)
                      hsame ∧
                    UnaryHistory auditRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeLocalDyadic dyadicProvenanceStream streamNormalRegSeq
    regSeqTransportReal realLocalAudit auditReadPkg
  obtain ⟨_strongNormUnary, normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have dyadicFaceUnary : UnaryHistory dyadicFace :=
    unary_cont_closed routeUnary localNameUnary routeLocalDyadic
  have streamFaceUnary : UnaryHistory streamFace :=
    unary_cont_closed dyadicFaceUnary provenanceUnary dyadicProvenanceStream
  have regSeqRatFaceUnary : UnaryHistory regSeqRatFace :=
    unary_cont_closed streamFaceUnary normalFormUnary streamNormalRegSeq
  have realFaceUnary : UnaryHistory realFace :=
    unary_cont_closed regSeqRatFaceUnary transportUnary regSeqTransportReal
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed realFaceUnary localNameUnary realLocalAudit
  have auditReadSource :
      (fun row : BHist => hsame row auditRead ∧ UnaryHistory row) auditRead := by
    exact ⟨hsame_refl auditRead, auditReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadicFace ∨ hsame row streamFace ∨ hsame row regSeqRatFace ∨
              hsame row realFace ∨ hsame row auditRead)
          (fun row : BHist =>
            hsame row auditRead ∧ PkgSig bundle auditRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead auditReadSource
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
      exact ⟨source.left, auditReadPkg, provenancePkg⟩
  }
  exact ⟨cert, auditReadUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
