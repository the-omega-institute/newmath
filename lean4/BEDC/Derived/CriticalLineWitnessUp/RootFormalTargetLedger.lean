import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessRootFormalTargetLedger {Z S M R Q H C P N terminal : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont N Q terminal →
        SemanticNameCert
            (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                  hsame row terminal)
            (fun row : BHist =>
              hsame row terminal ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧
                Cont N Q terminal ∧ hsame H (append Z S))
            hsame ∧
          UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ UnaryHistory terminal := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet terminalRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨_unaryZ, _unaryS, _unaryM, _unaryR, _unaryP, sameH, routeQ, routeC,
    routeN⟩ := packet
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed routeClosure.right.right.left routeClosure.left terminalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row terminal)
          (fun row : BHist =>
            hsame row terminal ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧
              Cont N Q terminal ∧ hsame H (append Z S))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminal ⟨hsame_refl terminal, terminalUnary⟩
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
      exact ⟨source.left, routeQ, routeC, routeN, terminalRoute, sameH⟩
  }
  exact
    ⟨cert, routeClosure.left, routeClosure.right.left, routeClosure.right.right.left,
      terminalUnary⟩

end BEDC.Derived.CriticalLineWitnessUp
