import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessLedgerNonescapeObligation
    {Z S M R Q H C P N ledgerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Q N ledgerRead →
        SemanticNameCert
            (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                  hsame row ledgerRead)
            (fun row : BHist =>
              hsame row ledgerRead ∧ Cont Q N ledgerRead ∧ Cont M R Q ∧
                Cont Q H C ∧ Cont C P N)
            hsame ∧
          UnaryHistory Q ∧ UnaryHistory N ∧ UnaryHistory ledgerRead ∧
            hsame H (append Z S) ∧ Cont Q N ledgerRead ∧ Cont M R Q ∧ Cont Q H C ∧
              Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet ledgerRoute
  have closure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨_unaryZ, _unaryS, _unaryM, _unaryR, _unaryP, _sameH, routeQ, routeC, routeN⟩ :=
    packet
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed closure.left closure.right.right.left ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row ledgerRead)
          (fun row : BHist =>
            hsame row ledgerRead ∧ Cont Q N ledgerRead ∧ Cont M R Q ∧
              Cont Q H C ∧ Cont C P N)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, ledgerRoute, routeQ, routeC, routeN⟩
  }
  exact
    ⟨cert, closure.left, closure.right.right.left, ledgerUnary, closure.right.right.right,
      ledgerRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
