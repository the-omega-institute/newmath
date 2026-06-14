import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_zero_strip_carrier_row
    {Z S M R Q H C P N rootRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) (append M R) rootRead ->
        SemanticNameCert
            (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row rootRead ∧ Cont (append Z S) (append M R) rootRead)
            (fun row : BHist => hsame row rootRead ∧ hsame H (append Z S) ∧ Cont M R Q)
            hsame ∧
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
            UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory rootRead ∧
              hsame H (append Z S) ∧ Cont (append Z S) (append M R) rootRead ∧
                Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet rootRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryZS : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryMR : UnaryHistory (append M R) :=
    unary_cont_closed unaryM unaryR (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport unaryZS (hsame_symm sameH)
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed unaryZS unaryMR rootRoute
  have sourceAtRoot : hsame rootRead rootRead ∧ UnaryHistory rootRead :=
    ⟨hsame_refl rootRead, rootUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row rootRead ∧ Cont (append Z S) (append M R) rootRead)
          (fun row : BHist =>
            hsame row rootRead ∧ hsame H (append Z S) ∧ Cont M R Q)
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
      exact ⟨source.left, rootRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sameH, routeQ⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, rootUnary, sameH,
      rootRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
