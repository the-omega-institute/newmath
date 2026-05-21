import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_ledger_nonescape
    {Z S M R Q H C P N stripRead zeroRead ledgerRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont stripRead Q zeroRead ->
          Cont zeroRead N ledgerRead ->
            Cont ledgerRead C refusalRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row refusalRead ∧ Cont Z S stripRead ∧ Cont stripRead Q zeroRead)
                  (fun row : BHist => hsame row refusalRead ∧ Cont ledgerRead C refusalRead)
                  hsame ∧
                UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory C ∧
                  UnaryHistory N ∧ UnaryHistory stripRead ∧ UnaryHistory zeroRead ∧
                    UnaryHistory ledgerRead ∧ UnaryHistory refusalRead ∧
                      hsame H (append Z S) ∧ Cont Z S stripRead ∧
                        Cont stripRead Q zeroRead ∧ Cont zeroRead N ledgerRead ∧
                          Cont ledgerRead C refusalRead ∧ Cont M R Q ∧ Cont Q H C ∧
                            Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet stripRoute zeroRoute ledgerRoute refusalRoute
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
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed stripUnary unaryQ zeroRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed zeroUnary unaryN ledgerRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed ledgerUnary unaryC refusalRoute
  have sourceAtRefusal : hsame refusalRead refusalRead ∧ UnaryHistory refusalRead :=
    ⟨hsame_refl refusalRead, refusalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row refusalRead ∧ Cont Z S stripRead ∧ Cont stripRead Q zeroRead)
          (fun row : BHist => hsame row refusalRead ∧ Cont ledgerRead C refusalRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead sourceAtRefusal
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
      exact ⟨source.left, stripRoute, zeroRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, refusalRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, unaryC, unaryN, stripUnary, zeroUnary, ledgerUnary,
      refusalUnary, sameH, stripRoute, zeroRoute, ledgerRoute, refusalRoute, routeQ,
      routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
