import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_refusal_ledger_pullback
    {Z S M R Q H C P N budgetRead selectorRead refusalRead rhRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q budgetRead ->
        Cont budgetRead N selectorRead ->
          Cont selectorRead C refusalRead ->
            Cont refusalRead Q rhRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row rhRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row rhRead ∧ Cont budgetRead N selectorRead ∧
                      Cont selectorRead C refusalRead)
                  (fun row : BHist => hsame row rhRead ∧ Cont refusalRead Q rhRead)
                  hsame ∧
                UnaryHistory budgetRead ∧ UnaryHistory selectorRead ∧
                  UnaryHistory refusalRead ∧ UnaryHistory rhRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory CriticalLineWitnessCarrier
  intro packet budgetRoute selectorRoute refusalRoute rhRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryAppend : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport unaryAppend (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed unaryAppend unaryQ budgetRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed budgetUnary unaryN selectorRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed selectorUnary unaryC refusalRoute
  have rhUnary : UnaryHistory rhRead :=
    unary_cont_closed refusalUnary unaryQ rhRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rhRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row rhRead ∧ Cont budgetRead N selectorRead ∧
              Cont selectorRead C refusalRead)
          (fun row : BHist => hsame row rhRead ∧ Cont refusalRead Q rhRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rhRead ⟨hsame_refl rhRead, rhUnary⟩
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
      exact ⟨source.left, selectorRoute, refusalRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, rhRoute⟩
  }
  exact ⟨cert, budgetUnary, selectorUnary, refusalUnary, rhUnary⟩

end BEDC.Derived.CriticalLineWitnessUp
