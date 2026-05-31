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

theorem MetaCICCriticalPathCandidateMediatedSNL10Readback [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadicRead streamRead regseqRead realRead phaseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName dyadicRead →
        Cont dyadicRead handoff streamRead →
          Cont streamRead transport regseqRead →
            Cont regseqRead normalForm realRead →
              Cont realRead dischargeSocket phaseRead →
                PkgSig bundle phaseRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row dyadicRead ∨ hsame row streamRead ∨
                          hsame row regseqRead ∨ hsame row realRead ∨
                            hsame row phaseRead ∨ hsame row dischargeSocket) ∧
                          UnaryHistory row)
                      (fun row : BHist =>
                        hsame row dyadicRead ∨ hsame row streamRead ∨
                          hsame row regseqRead ∨ hsame row realRead ∨
                            hsame row phaseRead ∨ hsame row dischargeSocket)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle phaseRead pkg)
                      hsame ∧
                    UnaryHistory dyadicRead ∧ UnaryHistory streamRead ∧
                      UnaryHistory regseqRead ∧ UnaryHistory realRead ∧
                        UnaryHistory phaseRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeLocalDyadic dyadicHandoffStream streamTransportRegseq
    regseqNormalReal realDischargePhase phasePkg
  obtain ⟨_strongNormUnary, normalFormUnary, _obstructionUnary, handoffUnary,
    dischargeSocketUnary, transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, transportLocalName,
    provenancePkg⟩ := packet
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed routeUnary localNameUnary routeLocalDyadic
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed dyadicUnary handoffUnary dyadicHandoffStream
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamUnary transportUnary streamTransportRegseq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regseqUnary normalFormUnary regseqNormalReal
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed realUnary dischargeSocketUnary realDischargePhase
  have sourceDyadic :
      (fun row : BHist =>
        (hsame row dyadicRead ∨ hsame row streamRead ∨ hsame row regseqRead ∨
          hsame row realRead ∨ hsame row phaseRead ∨ hsame row dischargeSocket) ∧
          UnaryHistory row) dyadicRead := by
    exact ⟨Or.inl (hsame_refl dyadicRead), dyadicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row dyadicRead ∨ hsame row streamRead ∨ hsame row regseqRead ∨
              hsame row realRead ∨ hsame row phaseRead ∨ hsame row dischargeSocket) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadicRead ∨ hsame row streamRead ∨ hsame row regseqRead ∨
              hsame row realRead ∨ hsame row phaseRead ∨ hsame row dischargeSocket)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle phaseRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro dyadicRead sourceDyadic
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
        constructor
        · cases source.left with
          | inl sameDyadic =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameDyadic)
          | inr tail =>
              cases tail with
              | inl sameStream =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameStream))
              | inr tail =>
                  cases tail with
                  | inl sameRegseq =>
                      exact Or.inr (Or.inr (Or.inl
                        (hsame_trans (hsame_symm sameRows) sameRegseq)))
                  | inr tail =>
                      cases tail with
                      | inl sameReal =>
                          exact Or.inr (Or.inr (Or.inr (Or.inl
                            (hsame_trans (hsame_symm sameRows) sameReal))))
                      | inr tail =>
                          cases tail with
                          | inl samePhase =>
                              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                                (hsame_trans (hsame_symm sameRows) samePhase)))))
                          | inr sameSocket =>
                              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                (hsame_trans (hsame_symm sameRows) sameSocket)))))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, phasePkg⟩
  }
  exact ⟨cert, dyadicUnary, streamUnary, regseqUnary, realUnary, phaseUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
