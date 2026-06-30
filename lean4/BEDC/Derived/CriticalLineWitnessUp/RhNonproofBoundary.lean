import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rh_nonproof_boundary
    {Z S M R Q H C P N refusalRead rhBoundary : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N Q refusalRead ->
        Cont refusalRead H rhBoundary ->
          SemanticNameCert
              (fun row : BHist => hsame row rhBoundary ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                  hsame row Q ∨ hsame row H ∨ hsame row N ∨ hsame row rhBoundary)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont N Q refusalRead ∧ Cont refusalRead H rhBoundary)
              hsame ∧
            UnaryHistory refusalRead ∧ UnaryHistory rhBoundary ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet refusalRoute boundaryRoute
  obtain ⟨unaryQ, _unaryC, unaryN, sameH⟩ :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  have unaryH : UnaryHistory H :=
    unary_transport
      (unary_cont_closed packet.left packet.right.left (cont_intro rfl))
      (hsame_symm sameH)
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have boundaryUnary : UnaryHistory rhBoundary :=
    unary_cont_closed refusalUnary unaryH boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rhBoundary ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
              hsame row Q ∨ hsame row H ∨ hsame row N ∨ hsame row rhBoundary)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont N Q refusalRead ∧ Cont refusalRead H rhBoundary)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro rhBoundary ⟨hsame_refl rhBoundary, boundaryUnary⟩
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
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, refusalRoute, boundaryRoute⟩
  }
  exact ⟨cert, refusalUnary, boundaryUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
