import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_fixed_strip_obstruction_exactness
    {Z S M R Q H C P N obstructionRead fixedRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S obstructionRead ->
        Cont obstructionRead N fixedRead ->
          SemanticNameCert
              (fun row : BHist => hsame row fixedRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row fixedRead)
              (fun row : BHist => hsame row fixedRead ∧ Cont obstructionRead N fixedRead)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory N ∧
              UnaryHistory obstructionRead ∧ UnaryHistory fixedRead ∧
                hsame H (append Z S) ∧ Cont Z S obstructionRead ∧
                  Cont obstructionRead N fixedRead ∧ Cont M R Q ∧ Cont Q H C ∧
                    Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet obstructionRoute fixedRoute
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
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed unaryZ unaryS obstructionRoute
  have fixedUnary : UnaryHistory fixedRead :=
    unary_cont_closed obstructionUnary unaryN fixedRoute
  have sourceAtFixed : hsame fixedRead fixedRead ∧ UnaryHistory fixedRead :=
    ⟨hsame_refl fixedRead, fixedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row fixedRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row fixedRead)
          (fun row : BHist => hsame row fixedRead ∧ Cont obstructionRead N fixedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro fixedRead sourceAtFixed
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, fixedRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, unaryN, obstructionUnary, fixedUnary, sameH,
      obstructionRoute, fixedRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
