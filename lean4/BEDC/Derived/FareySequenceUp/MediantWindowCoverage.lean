import BEDC.Derived.FareySequenceUp.TasteGate

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceMediantWindowCoverage [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N adjacentRead mediantRead levelRead
      toleranceRead approximationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont B A adjacentRead ->
        Cont adjacentRead M mediantRead ->
          Cont mediantRead L levelRead ->
            Cont levelRead T toleranceRead ->
              Cont toleranceRead G approximationRead ->
                PkgSig bundle N pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row adjacentRead ∨ hsame row mediantRead ∨
                            hsame row levelRead) ∧
                          UnaryHistory row)
                      (fun row : BHist =>
                        hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨
                          hsame row T ∨ hsame row G ∨ hsame row adjacentRead ∨
                            hsame row mediantRead ∨ hsame row levelRead ∨
                              hsame row toleranceRead ∨ hsame row approximationRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont B A adjacentRead ∧
                          Cont adjacentRead M mediantRead ∧ Cont mediantRead L levelRead ∧
                            Cont levelRead T toleranceRead ∧
                              Cont toleranceRead G approximationRead ∧ PkgSig bundle N pkg)
                      hsame ∧
                    UnaryHistory adjacentRead ∧ UnaryHistory mediantRead ∧
                      UnaryHistory levelRead ∧ UnaryHistory toleranceRead ∧
                        UnaryHistory approximationRead := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier adjacentRoute mediantRoute levelRoute toleranceRoute approximationRoute namePkg
  obtain ⟨bUnary, aUnary, mUnary, lUnary, tUnary, _sUnary, _dUnary, _qUnary,
    _wUnary, _rUnary, gUnary, _eUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _aEmpty, _sEmpty, _mEmpty, _gEmpty, _eEmpty, _provenancePkg⟩ := carrier
  have adjacentUnary : UnaryHistory adjacentRead :=
    unary_cont_closed bUnary aUnary adjacentRoute
  have mediantUnary : UnaryHistory mediantRead :=
    unary_cont_closed adjacentUnary mUnary mediantRoute
  have levelUnary : UnaryHistory levelRead :=
    unary_cont_closed mediantUnary lUnary levelRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed levelUnary tUnary toleranceRoute
  have approximationUnary : UnaryHistory approximationRead :=
    unary_cont_closed toleranceUnary gUnary approximationRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row adjacentRead ∨ hsame row mediantRead ∨ hsame row levelRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨
              hsame row T ∨ hsame row G ∨ hsame row adjacentRead ∨
                hsame row mediantRead ∨ hsame row levelRead ∨
                  hsame row toleranceRead ∨ hsame row approximationRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B A adjacentRead ∧
              Cont adjacentRead M mediantRead ∧ Cont mediantRead L levelRead ∧
                Cont levelRead T toleranceRead ∧
                  Cont toleranceRead G approximationRead ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro levelRead ⟨Or.inr (Or.inr (hsame_refl levelRead)), levelUnary⟩
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
          | inl sameAdjacent =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameAdjacent)
          | inr tail =>
              cases tail with
              | inl sameMediant =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameMediant))
              | inr sameLevel =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameLevel))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameAdjacent =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameAdjacent))))))
      | inr tail =>
          cases tail with
          | inl sameMediant =>
              exact Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameMediant)))))))
          | inr sameLevel =>
              exact Or.inr
                (Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameLevel))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, adjacentRoute, mediantRoute, levelRoute, toleranceRoute,
          approximationRoute, namePkg⟩
  }
  exact
    ⟨cert, adjacentUnary, mediantUnary, levelUnary, toleranceUnary, approximationUnary⟩

end BEDC.Derived.FareySequenceUp
