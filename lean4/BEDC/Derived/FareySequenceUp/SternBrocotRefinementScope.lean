import BEDC.Derived.FareySequenceUp.TasteGate

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceSternBrocotRefinementScope [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N adjacentRead refinementRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg →
      Cont A M adjacentRead →
        Cont adjacentRead S refinementRead →
          Cont refinementRead N namedRead →
            PkgSig bundle N pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row refinementRead ∨ hsame row namedRead)
                  (fun row : BHist =>
                    hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row S ∨
                      hsame row adjacentRead ∨ hsame row refinementRead ∨
                        hsame row namedRead)
                  (fun row : BHist =>
                    PkgSig bundle N pkg ∧
                      (hsame row refinementRead ∨ hsame row namedRead))
                  hsame ∧ UnaryHistory adjacentRead ∧ UnaryHistory refinementRead ∧
                UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier adjacentRoute refinementRoute namedRoute pkgN
  obtain ⟨_bUnary, aUnary, mUnary, _lUnary, _tUnary, sUnary, _dUnary, _qUnary,
    _wUnary, _rUnary, _gUnary, _eUnary, _hUnary, _cUnary, _pUnary, nUnary,
    _aEmpty, _sEmpty, _mEmpty, _gEmpty, _eEmpty, _carrierPkg⟩ := carrier
  have adjacentUnary : UnaryHistory adjacentRead :=
    unary_cont_closed aUnary mUnary adjacentRoute
  have refinementUnary : UnaryHistory refinementRead :=
    unary_cont_closed adjacentUnary sUnary refinementRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed refinementUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refinementRead ∨ hsame row namedRead)
          (fun row : BHist =>
            hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row S ∨
              hsame row adjacentRead ∨ hsame row refinementRead ∨ hsame row namedRead)
          (fun row : BHist =>
            PkgSig bundle N pkg ∧ (hsame row refinementRead ∨ hsame row namedRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refinementRead (Or.inl (hsame_refl refinementRead))
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
        cases source with
        | inl sameRefinement =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameRefinement)
        | inr sameNamed =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameNamed)
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameRefinement =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameRefinement)))))
      | inr sameNamed =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameNamed)))))
    ledger_sound := by
      intro _row source
      exact ⟨pkgN, source⟩
  }
  exact ⟨cert, adjacentUnary, refinementUnary, namedUnary⟩

end BEDC.Derived.FareySequenceUp
