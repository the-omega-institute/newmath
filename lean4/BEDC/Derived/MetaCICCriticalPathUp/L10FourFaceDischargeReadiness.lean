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

theorem MetaCICCriticalPathL10FourFaceDischargeReadiness [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadicFace streamFace regSeqRatFace realFace dischargeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route provenance dyadicFace →
        Cont dyadicFace localName streamFace →
          Cont streamFace normalForm regSeqRatFace →
            Cont regSeqRatFace transport realFace →
              Cont realFace dischargeSocket dischargeRead →
                PkgSig bundle dischargeRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row dischargeRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row dyadicFace ∨ hsame row streamFace ∨
                          hsame row regSeqRatFace ∨ hsame row realFace ∨
                            hsame row dischargeRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont realFace dischargeSocket dischargeRead ∧
                          PkgSig bundle dischargeRead pkg)
                      hsame ∧
                    UnaryHistory dischargeRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet routeProvenanceDyadic dyadicLocalNameStream streamNormalFormRegSeq
    regSeqTransportReal realDischargeRead dischargePkg
  obtain ⟨_strongNormUnary, normalFormUnary, _obstructionUnary, _handoffUnary,
    dischargeSocketUnary, transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have dyadicUnary : UnaryHistory dyadicFace :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceDyadic
  have streamUnary : UnaryHistory streamFace :=
    unary_cont_closed dyadicUnary localNameUnary dyadicLocalNameStream
  have regSeqUnary : UnaryHistory regSeqRatFace :=
    unary_cont_closed streamUnary normalFormUnary streamNormalFormRegSeq
  have realUnary : UnaryHistory realFace :=
    unary_cont_closed regSeqUnary transportUnary regSeqTransportReal
  have dischargeUnary : UnaryHistory dischargeRead :=
    unary_cont_closed realUnary dischargeSocketUnary realDischargeRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row dischargeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadicFace ∨ hsame row streamFace ∨ hsame row regSeqRatFace ∨
              hsame row realFace ∨ hsame row dischargeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont realFace dischargeSocket dischargeRead ∧
              PkgSig bundle dischargeRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro dischargeRead ⟨hsame_refl dischargeRead, dischargeUnary⟩
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
      exact ⟨source.right, realDischargeRead, dischargePkg⟩
  }
  exact ⟨cert, dischargeUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
