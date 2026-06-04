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

theorem MetaCICCriticalPathCandidateResidualL10FrontierRoute [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName candidateFrontier dyadicRead streamRead regseqRead realSeal
      residualRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont handoff dischargeSocket candidateFrontier →
        Cont candidateFrontier route dyadicRead →
          Cont dyadicRead provenance streamRead →
            Cont streamRead normalForm regseqRead →
              Cont regseqRead dischargeSocket realSeal →
                Cont realSeal obstruction residualRead →
                  PkgSig bundle residualRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row residualRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row candidateFrontier ∨ hsame row dyadicRead ∨
                            hsame row streamRead ∨ hsame row regseqRead ∨
                              hsame row realSeal ∨ hsame row residualRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle residualRead pkg ∧
                            Cont realSeal obstruction residualRead)
                        hsame ∧
                      UnaryHistory candidateFrontier ∧ UnaryHistory residualRead ∧
                        PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet handoffSocketFrontier frontierRouteDyadic dyadicProvenanceStream
    streamNormalRegseq regseqSocketRealSeal realSealObstructionResidual residualPkg
  obtain ⟨_strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have candidateFrontierUnary : UnaryHistory candidateFrontier :=
    unary_cont_closed handoffUnary dischargeSocketUnary handoffSocketFrontier
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed candidateFrontierUnary routeUnary frontierRouteDyadic
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed dyadicReadUnary provenanceUnary dyadicProvenanceStream
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamReadUnary normalFormUnary streamNormalRegseq
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regseqReadUnary dischargeSocketUnary regseqSocketRealSeal
  have residualReadUnary : UnaryHistory residualRead :=
    unary_cont_closed realSealUnary obstructionUnary realSealObstructionResidual
  have sourceResidual :
      (fun row : BHist => hsame row residualRead ∧ UnaryHistory row) residualRead := by
    exact ⟨hsame_refl residualRead, residualReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row residualRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateFrontier ∨ hsame row dyadicRead ∨ hsame row streamRead ∨
              hsame row regseqRead ∨ hsame row realSeal ∨ hsame row residualRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle residualRead pkg ∧
              Cont realSeal obstruction residualRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro residualRead sourceResidual
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
      exact ⟨source.right, residualPkg, realSealObstructionResidual⟩
  }
  exact ⟨cert, candidateFrontierUnary, residualReadUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
