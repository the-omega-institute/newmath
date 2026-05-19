import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_obligation_completion_packet
    {Z S M R Q H C P N obligationRead ledgerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont H C obligationRead ->
        Cont obligationRead N ledgerRead ->
          SemanticNameCert
              (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row ledgerRead ∧ hsame H (append Z S) ∧
                  Cont H C obligationRead)
              (fun row : BHist =>
                hsame row ledgerRead ∧ Cont obligationRead N ledgerRead)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory N ∧
                UnaryHistory obligationRead ∧ UnaryHistory ledgerRead ∧
                  hsame H (append Z S) ∧ Cont H C obligationRead ∧
                    Cont obligationRead N ledgerRead ∧ Cont M R Q ∧ Cont Q H C ∧
                      Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet obligationRoute ledgerRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have obligationUnary : UnaryHistory obligationRead :=
    unary_cont_closed unaryH routeClosure.right.left obligationRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed obligationUnary routeClosure.right.right.left ledgerRoute
  have sourceAtLedger : hsame ledgerRead ledgerRead ∧ UnaryHistory ledgerRead :=
    ⟨hsame_refl ledgerRead, ledgerUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row ledgerRead ∧ hsame H (append Z S) ∧ Cont H C obligationRead)
        (fun row : BHist => hsame row ledgerRead ∧ Cont obligationRead N ledgerRead)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead sourceAtLedger
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
      exact ⟨source.left, sameH, obligationRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, ledgerRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, routeClosure.left, unaryH,
      routeClosure.right.left, routeClosure.right.right.left, obligationUnary, ledgerUnary,
      sameH, obligationRoute, ledgerRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
