import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_scoped_ledger_exactness
    {Z S M R Q H C P N scopedRead ledgerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S scopedRead ->
        Cont scopedRead Q ledgerRead ->
          SemanticNameCert
              (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row scopedRead ∨ hsame row Q ∨ hsame row ledgerRead)
              (fun row : BHist => hsame row ledgerRead ∧ Cont scopedRead Q ledgerRead)
              hsame ∧
            UnaryHistory scopedRead ∧ UnaryHistory ledgerRead ∧ hsame H (append Z S) ∧
              Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet scopedRoute ledgerRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed unaryZ unaryS scopedRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed scopedUnary (unary_cont_closed unaryM unaryR routeQ) ledgerRoute
  have sourceAtLedger : hsame ledgerRead ledgerRead ∧ UnaryHistory ledgerRead :=
    ⟨hsame_refl ledgerRead, ledgerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row scopedRead ∨ hsame row Q ∨ hsame row ledgerRead)
          (fun row : BHist => hsame row ledgerRead ∧ Cont scopedRead Q ledgerRead)
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, ledgerRoute⟩
  }
  exact ⟨cert, scopedUnary, ledgerUnary, sameH, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
