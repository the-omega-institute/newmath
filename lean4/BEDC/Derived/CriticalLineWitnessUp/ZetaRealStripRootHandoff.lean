import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zeta_real_strip_root_handoff
    {Z S M R Q H C P N zetaRead realRead stripRead rootRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont M R realRead ->
          Cont zetaRead realRead stripRead ->
            Cont stripRead N rootRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                      hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                        hsame row N ∨ hsame row rootRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont Z S zetaRead ∧ Cont M R realRead ∧
                      Cont zetaRead realRead stripRead ∧ Cont stripRead N rootRead)
                  hsame ∧
                UnaryHistory zetaRead ∧ UnaryHistory realRead ∧ UnaryHistory stripRead ∧
                  UnaryHistory rootRead ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory CriticalLineWitnessCarrier
  intro packet zetaRoute realRoute stripRoute rootRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have appendUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport appendUnary (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have zetaUnary : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed unaryM unaryR realRoute
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed zetaUnary realUnary stripRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed stripUnary unaryN rootRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row rootRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S zetaRead ∧ Cont M R realRead ∧
              Cont zetaRead realRead stripRead ∧ Cont stripRead N rootRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rootRead ⟨hsame_refl rootRead, rootUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, zetaRoute, realRoute, stripRoute, rootRoute⟩
  }
  exact ⟨cert, zetaUnary, realUnary, stripUnary, rootUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
