import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_line_row_exposure
    {Z S M R Q H C P N rootRead stripRead modulusRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N -> Cont Z S stripRead ->
      Cont M R modulusRead -> Cont stripRead modulusRead rootRead ->
        SemanticNameCert
            (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row rootRead ∧ Cont Z S stripRead ∧ Cont M R modulusRead)
            (fun row : BHist =>
              hsame row rootRead ∧ Cont stripRead modulusRead rootRead)
            hsame ∧
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
            UnaryHistory stripRead ∧ UnaryHistory modulusRead ∧ UnaryHistory rootRead ∧
              hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet stripRoute modulusRoute rootRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, _routeQ, _routeC, _routeN⟩ :=
    packet
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed stripUnary modulusUnary rootRoute
  have sourceAtRoot : hsame rootRead rootRead ∧ UnaryHistory rootRead :=
    ⟨hsame_refl rootRead, rootUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row rootRead ∧ Cont Z S stripRead ∧ Cont M R modulusRead)
          (fun row : BHist =>
            hsame row rootRead ∧ Cont stripRead modulusRead rootRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rootRead sourceAtRoot
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
      exact ⟨source.left, stripRoute, modulusRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, rootRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, stripUnary, modulusUnary, rootUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
