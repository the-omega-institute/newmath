import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_modulus_classifier_exhaustion
    {Z S M R Q H C P N modulusRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R modulusRead ->
        SemanticNameCert
            (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row M ∨ hsame row R ∨ hsame row Q ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row modulusRead)
            (fun row : BHist => hsame row modulusRead ∧ Cont M R modulusRead)
            hsame ∧
          UnaryHistory modulusRead ∧ UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧
            hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet modulusRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨_unaryZ, _unaryS, unaryM, unaryR, _unaryP, _sameH, _routeQ, _routeC,
    _routeN⟩ := packet
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row Q ∨ hsame row H ∨ hsame row C ∨
              hsame row P ∨ hsame row N ∨ hsame row modulusRead)
          (fun row : BHist => hsame row modulusRead ∧ Cont M R modulusRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro modulusRead
        ⟨hsame_refl modulusRead, modulusReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, modulusRoute⟩
  }
  exact
    ⟨cert, modulusReadUnary, routeClosure.left, routeClosure.right.left,
      routeClosure.right.right.left, routeClosure.right.right.right⟩

end BEDC.Derived.CriticalLineWitnessUp
