import BEDC.Derived.FareySequenceUp.TasteGate

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceFiniteMediantCoverage [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N boundaryRead inserted sternRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont B A boundaryRead ->
        Cont boundaryRead M inserted ->
          Cont inserted S sternRead ->
            PkgSig bundle inserted pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row inserted ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row A ∨ hsame row S ∨ hsame row L ∨ hsame row T ∨
                      hsame row inserted ∨ hsame row sternRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont boundaryRead M inserted ∧
                      Cont inserted S sternRead ∧ PkgSig bundle inserted pkg)
                  hsame ∧
                UnaryHistory boundaryRead ∧ UnaryHistory inserted ∧
                  UnaryHistory sternRead := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert
  intro carrier boundaryRoute insertedRoute sternRoute insertedPkg
  obtain ⟨bUnary, aUnary, mUnary, _lUnary, _tUnary, sUnary, _dUnary, _qUnary,
    _wUnary, _rUnary, _gUnary, _eUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _aEmpty, _sEmpty, _mEmpty, _gEmpty, _eEmpty, _provenancePkg⟩ := carrier
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed bUnary aUnary boundaryRoute
  have insertedUnary : UnaryHistory inserted :=
    unary_cont_closed boundaryReadUnary mUnary insertedRoute
  have sternReadUnary : UnaryHistory sternRead :=
    unary_cont_closed insertedUnary sUnary sternRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row inserted ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row S ∨ hsame row L ∨ hsame row T ∨
              hsame row inserted ∨ hsame row sternRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont boundaryRead M inserted ∧
              Cont inserted S sternRead ∧ PkgSig bundle inserted pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro inserted ⟨hsame_refl inserted, insertedUnary⟩
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
      exact ⟨source.right, insertedRoute, sternRoute, insertedPkg⟩
  }
  exact ⟨cert, boundaryReadUnary, insertedUnary, sternReadUnary⟩

end BEDC.Derived.FareySequenceUp
