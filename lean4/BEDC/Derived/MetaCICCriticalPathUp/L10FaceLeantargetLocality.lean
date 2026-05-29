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

theorem MetaCICCriticalPathL10FaceLeantargetLocality [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadic stream regseq realSeal faceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName dyadic →
        Cont dyadic localName stream →
          Cont stream localName regseq →
            Cont regseq localName realSeal →
              Cont realSeal localName faceRead →
                PkgSig bundle faceRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                          hsame row realSeal ∨ hsame row faceRead) ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                          hsame row realSeal ∨ hsame row faceRead)
                      (fun row : BHist =>
                        (hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                          hsame row realSeal ∨ hsame row faceRead) ∧
                          PkgSig bundle provenance pkg)
                      hsame ∧
                    UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory regseq ∧
                      UnaryHistory realSeal ∧ UnaryHistory faceRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeLocalDyadic dyadicLocalStream streamLocalRegseq regseqLocalRealSeal
    realSealLocalFaceRead _faceReadPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have dyadicUnary : UnaryHistory dyadic :=
    unary_cont_closed routeUnary localNameUnary routeLocalDyadic
  have streamUnary : UnaryHistory stream :=
    unary_cont_closed dyadicUnary localNameUnary dyadicLocalStream
  have regseqUnary : UnaryHistory regseq :=
    unary_cont_closed streamUnary localNameUnary streamLocalRegseq
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regseqUnary localNameUnary regseqLocalRealSeal
  have faceReadUnary : UnaryHistory faceRead :=
    unary_cont_closed realSealUnary localNameUnary realSealLocalFaceRead
  have sourceDyadic :
      (fun row : BHist =>
        (hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
          hsame row realSeal ∨ hsame row faceRead) ∧ UnaryHistory row) dyadic := by
    exact ⟨Or.inl (hsame_refl dyadic), dyadicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row faceRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row faceRead)
          (fun row : BHist =>
            (hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row faceRead) ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro dyadic sourceDyadic
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
        cases source.left with
        | inl sameDyadic =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameDyadic),
                unary_transport source.right sameRows⟩
        | inr rest =>
            cases rest with
            | inl sameStream =>
                exact
                  ⟨Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameStream)),
                    unary_transport source.right sameRows⟩
            | inr rest =>
                cases rest with
                | inl sameRegseq =>
                    exact
                      ⟨Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameRegseq))),
                        unary_transport source.right sameRows⟩
                | inr rest =>
                    cases rest with
                    | inl sameRealSeal =>
                        exact
                          ⟨Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inl
                                    (hsame_trans (hsame_symm sameRows) sameRealSeal)))),
                            unary_transport source.right sameRows⟩
                    | inr sameFaceRead =>
                        exact
                          ⟨Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (hsame_trans (hsame_symm sameRows) sameFaceRead)))),
                            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact ⟨cert, dyadicUnary, streamUnary, regseqUnary, realSealUnary, faceReadUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
