import BEDC.Derived.RegularCauchyApartnessBudgetUp.TasteGate

namespace BEDC.Derived.RegularCauchyApartnessBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyApartnessBudgetCarrier_phase_real_handoff [AskSetup] [PackageSetup]
    {X A M W D R E H C P N budgetWindow lowerRead regularRead realExit phaseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyApartnessBudgetCarrier X A M W D R E H C P N bundle pkg ->
      Cont A M budgetWindow ->
        Cont budgetWindow D lowerRead ->
          Cont lowerRead R regularRead ->
            Cont regularRead E realExit ->
              Cont realExit P phaseRead ->
                PkgSig bundle phaseRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row phaseRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row X ∨ hsame row A ∨ hsame row M ∨ hsame row W ∨
                          hsame row D ∨ hsame row R ∨ hsame row E ∨
                            Cont realExit P phaseRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont A M budgetWindow ∧
                          Cont budgetWindow D lowerRead ∧ Cont lowerRead R regularRead ∧
                            Cont regularRead E realExit ∧ Cont realExit P phaseRead ∧
                              PkgSig bundle phaseRead pkg)
                      hsame ∧
                    UnaryHistory phaseRead := by
  -- BEDC touchpoint anchor: RegularCauchyApartnessBudgetCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier budgetRoute lowerRoute regularRoute realExitRoute phaseRoute phasePkg
  obtain ⟨xUnary, aUnary, mUnary, _wUnary, dUnary, rUnary, eUnary, _hUnary,
    _cUnary, pUnary, _nUnary, _budgetWindow, _lowerReadback, _pkgP, _pkgN⟩ :=
      carrier
  have budgetUnary : UnaryHistory budgetWindow :=
    unary_cont_closed aUnary mUnary budgetRoute
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed budgetUnary dUnary lowerRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed lowerUnary rUnary regularRoute
  have realExitUnary : UnaryHistory realExit :=
    unary_cont_closed regularUnary eUnary realExitRoute
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed realExitUnary pUnary phaseRoute
  have _sourceUnary : UnaryHistory X := xUnary
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row phaseRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row A ∨ hsame row M ∨ hsame row W ∨ hsame row D ∨
              hsame row R ∨ hsame row E ∨ Cont realExit P phaseRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A M budgetWindow ∧ Cont budgetWindow D lowerRead ∧
              Cont lowerRead R regularRead ∧ Cont regularRead E realExit ∧
                Cont realExit P phaseRead ∧ PkgSig bundle phaseRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro phaseRead ⟨hsame_refl phaseRead, phaseUnary⟩
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
      intro _row _source
      right
      right
      right
      right
      right
      right
      right
      exact phaseRoute
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, budgetRoute, lowerRoute, regularRoute, realExitRoute, phaseRoute,
          phasePkg⟩
  }
  exact ⟨cert, phaseUnary⟩

end BEDC.Derived.RegularCauchyApartnessBudgetUp
