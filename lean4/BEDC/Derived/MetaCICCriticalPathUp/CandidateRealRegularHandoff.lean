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

theorem MetaCICCriticalPathCandidateRealRegularHandoff [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadicFace streamFace regSeqFace realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      UnaryHistory dyadicFace →
        UnaryHistory regSeqFace →
          Cont route dyadicFace streamFace →
            Cont streamFace regSeqFace realSeal →
              PkgSig bundle realSeal pkg →
                SemanticNameCert
                  (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row route ∨ hsame row dyadicFace ∨ hsame row streamFace ∨
                      hsame row regSeqFace ∨ hsame row realSeal)
                  (fun row : BHist =>
                    hsame row realSeal ∧ PkgSig bundle realSeal pkg ∧
                      PkgSig bundle provenance pkg)
                  hsame ∧
                  UnaryHistory route ∧ UnaryHistory streamFace ∧ UnaryHistory realSeal ∧
                    Cont route dyadicFace streamFace ∧
                      Cont streamFace regSeqFace realSeal ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet dyadicUnary regSeqUnary routeDyadicStream streamRegSeqReal realSealPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have streamUnary : UnaryHistory streamFace :=
    unary_cont_closed routeUnary dyadicUnary routeDyadicStream
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed streamUnary regSeqUnary streamRegSeqReal
  have sourceRealSeal :
      (fun row : BHist => hsame row realSeal ∧ UnaryHistory row) realSeal := by
    exact ⟨hsame_refl realSeal, realSealUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row route ∨ hsame row dyadicFace ∨ hsame row streamFace ∨
            hsame row regSeqFace ∨ hsame row realSeal)
        (fun row : BHist =>
          hsame row realSeal ∧ PkgSig bundle realSeal pkg ∧
            PkgSig bundle provenance pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal sourceRealSeal
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
      exact ⟨source.left, realSealPkg, provenancePkg⟩
  }
  exact
    ⟨cert, routeUnary, streamUnary, realSealUnary, routeDyadicStream, streamRegSeqReal,
      provenancePkg, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
