import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rh_nonclassification_boundary
    {Z S M R Q H C P N refusalRead rhRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N Q refusalRead ->
        Cont refusalRead C rhRead ->
          SemanticNameCert
              (fun row : BHist => hsame row rhRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row rhRead ∧ hsame H (append Z S))
              (fun row : BHist =>
                hsame row rhRead ∧ Cont N Q refusalRead ∧ Cont refusalRead C rhRead)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧
                UnaryHistory refusalRead ∧ UnaryHistory rhRead ∧
                  hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet refusalRoute rhRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have rhUnary : UnaryHistory rhRead :=
    unary_cont_closed refusalUnary unaryC rhRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rhRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row rhRead ∧ hsame H (append Z S))
          (fun row : BHist =>
            hsame row rhRead ∧ Cont N Q refusalRead ∧ Cont refusalRead C rhRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro rhRead ⟨hsame_refl rhRead, rhUnary⟩
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
      exact ⟨source.left, sameH⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, refusalRoute, rhRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryC, unaryN, refusalUnary,
      rhUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
