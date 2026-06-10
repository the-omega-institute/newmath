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

theorem MetaCICCriticalPathPhaseRealSourceObligations [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal sourceCut phaseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      Cont dyadic stream sourceCut ->
        Cont sourceCut regseq phaseRead ->
          PkgSig bundle phaseRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row phaseRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row dyadic ∨ hsame row stream ∨ hsame row sourceCut ∨
                    hsame row regseq ∨ hsame row realSeal ∨ hsame row phaseRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle phaseRead pkg ∧
                    PkgSig bundle realSeal pkg ∧ Cont sourceCut regseq phaseRead)
                hsame ∧
              UnaryHistory sourceCut ∧ UnaryHistory phaseRead ∧
                PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger dyadicStreamSourceCut sourceCutRegseqPhase phasePkg
  obtain ⟨_packet, dyadicUnary, streamUnary, regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  have sourceCutUnary : UnaryHistory sourceCut :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamSourceCut
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed sourceCutUnary regseqUnary sourceCutRegseqPhase
  have sourcePhase :
      (fun row : BHist => hsame row phaseRead ∧ UnaryHistory row) phaseRead := by
    exact ⟨hsame_refl phaseRead, phaseUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row phaseRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row sourceCut ∨
              hsame row regseq ∨ hsame row realSeal ∨ hsame row phaseRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle phaseRead pkg ∧
              PkgSig bundle realSeal pkg ∧ Cont sourceCut regseq phaseRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro phaseRead sourcePhase
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
      exact ⟨source.right, phasePkg, realSealPkg, sourceCutRegseqPhase⟩
  }
  exact ⟨cert, sourceCutUnary, phaseUnary, realSealPkg⟩

theorem MetaCICCriticalPathFormalTargetSurface [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            (hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle realSeal pkg)
          hsame ∧
        UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory regseq ∧
          UnaryHistory realSeal ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro ledger
  obtain ⟨_packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  have sourceWitness :
      (fun row : BHist =>
        (hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
          hsame row realSeal) ∧ UnaryHistory row) dyadic := by
    exact ⟨Or.inl (hsame_refl dyadic), dyadicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro dyadic sourceWitness
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
          | inl rowDyadic =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) rowDyadic)
          | inr rest =>
              cases rest with
              | inl rowStream =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowStream))
              | inr rest =>
                  cases rest with
                  | inl rowRegseq =>
                      exact Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowRegseq)))
                  | inr rowRealSeal =>
                      exact Or.inr
                        (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) rowRealSeal)))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, realSealPkg⟩
  }
  exact
    ⟨cert, dyadicUnary, streamUnary, regseqUnary, realSealUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
