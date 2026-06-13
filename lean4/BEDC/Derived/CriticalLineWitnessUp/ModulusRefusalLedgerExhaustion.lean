import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_modulus_refusal_ledger_exhaustion
    {Z S M R Q H C P N sourceRead modulusRead refusalRead ledgerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont sourceRead M modulusRead ->
          Cont modulusRead Q refusalRead ->
            Cont refusalRead H ledgerRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                      hsame row Q ∨ hsame row H ∨ hsame row ledgerRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont Z S sourceRead ∧
                      Cont sourceRead M modulusRead ∧ Cont modulusRead Q refusalRead ∧
                        Cont refusalRead H ledgerRead ∧ hsame H (append Z S))
                  hsame ∧
                UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute modulusRoute refusalRoute ledgerRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, _unaryR, _unaryP, sameH, _routeQ, _routeC, _routeN⟩ :=
    packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed sourceUnary unaryM modulusRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed modulusUnary routeClosure.left refusalRoute
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed refusalUnary unaryH ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row H ∨ hsame row ledgerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S sourceRead ∧ Cont sourceRead M modulusRead ∧
              Cont modulusRead Q refusalRead ∧ Cont refusalRead H ledgerRead ∧
                hsame H (append Z S))
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceRoute, modulusRoute, refusalRoute, ledgerRoute, sameH⟩
  }
  exact ⟨cert, ledgerUnary⟩

end BEDC.Derived.CriticalLineWitnessUp
