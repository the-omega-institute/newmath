import BEDC.Derived.FareySequenceUp.TasteGate

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceRegSeqRatDensityInduction [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N boundaryRead levelRead densityRead
      rationalRead windowRead readbackRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg →
      Cont B A boundaryRead →
        Cont boundaryRead M levelRead →
          Cont levelRead D densityRead →
            Cont densityRead Q rationalRead →
              Cont rationalRead W windowRead →
                Cont windowRead R readbackRead →
                  PkgSig bundle N pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row readbackRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row D ∨
                            hsame row Q ∨ hsame row W ∨ hsame row R ∨
                              hsame row readbackRead ∨ hsame row N)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont densityRead Q rationalRead ∧
                            Cont rationalRead W windowRead ∧
                              Cont windowRead R readbackRead ∧ PkgSig bundle N pkg)
                        hsame ∧
                      UnaryHistory boundaryRead ∧ UnaryHistory levelRead ∧
                        UnaryHistory densityRead ∧ UnaryHistory rationalRead ∧
                          UnaryHistory windowRead ∧ UnaryHistory readbackRead := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier boundaryRoute levelRoute densityRoute rationalRoute windowRoute readbackRoute pkgN
  obtain ⟨bUnary, aUnary, mUnary, _lUnary, _tUnary, _sUnary, dUnary, qUnary, wUnary,
    rUnary, _gUnary, _eUnary, _hUnary, _cUnary, _pUnary, nUnary, _aEmpty, _sEmpty,
    _mEmpty, _gEmpty, _eEmpty, _carrierPkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed bUnary aUnary boundaryRoute
  have levelUnary : UnaryHistory levelRead :=
    unary_cont_closed boundaryUnary mUnary levelRoute
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed levelUnary dUnary densityRoute
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed densityUnary qUnary rationalRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed rationalUnary wUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary rUnary readbackRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readbackRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row D ∨ hsame row Q ∨
              hsame row W ∨ hsame row R ∨ hsame row readbackRead ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont densityRead Q rationalRead ∧
              Cont rationalRead W windowRead ∧ Cont windowRead R readbackRead ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readbackRead ⟨hsame_refl readbackRead, readbackUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, rationalRoute, windowRoute, readbackRoute, pkgN⟩
  }
  exact
    ⟨cert, boundaryUnary, levelUnary, densityUnary, rationalUnary, windowUnary,
      readbackUnary⟩

end BEDC.Derived.FareySequenceUp
