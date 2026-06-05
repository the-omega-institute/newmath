import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalRealRegSeqRatScope [AskSetup] [PackageSetup]
    {C F eps B D W M H K P N realRead regseqRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface C F eps B D W M H K P N bundle pkg →
      Cont M H realRead →
        Cont realRead K regseqRead →
          PkgSig bundle P pkg →
            PkgSig bundle N pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row realRead ∨ hsame row regseqRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row C ∨ hsame row F ∨ hsame row eps ∨ hsame row B ∨
                      hsame row D ∨ hsame row W ∨ hsame row M ∨
                        hsame row realRead ∨ hsame row regseqRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont M H realRead ∧ Cont realRead K regseqRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                  hsame ∧
                UnaryHistory realRead ∧ UnaryHistory regseqRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier modulusReal realRegSeq provenancePkg namePkg
  obtain ⟨_cUnary, _fUnary, _epsUnary, _bUnary, _dUnary, _wUnary, modulusUnary,
    transportUnary, replayUnary, _provenanceUnary, _localNameUnary, _transportLocalName,
    _branchDepthWitness, _witnessModulusReplay, _carrierProvenancePkg⟩ := carrier
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed modulusUnary transportUnary modulusReal
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed realUnary replayUnary realRegSeq
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row realRead ∨ hsame row regseqRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row F ∨ hsame row eps ∨ hsame row B ∨
              hsame row D ∨ hsame row W ∨ hsame row M ∨
                hsame row realRead ∨ hsame row regseqRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M H realRead ∧ Cont realRead K regseqRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead ⟨Or.inl (hsame_refl realRead), realUnary⟩
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
          | inl realSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) realSame)
          | inr regseqSame =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) regseqSame)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl realSame =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl realSame)))))))
      | inr regseqSame =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr regseqSame)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, modulusReal, realRegSeq, provenancePkg, namePkg⟩
  }
  exact ⟨cert, realUnary, regseqUnary⟩

end BEDC.Derived.FanfunctionalUp
