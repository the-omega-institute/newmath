import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_modulus_request_factorization
    {Z S M R Q H C P N depthRead modulusRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont M R depthRead →
        Cont depthRead Q modulusRead →
          SemanticNameCert
              (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row R ∨ hsame row Q ∨ hsame row H ∨ hsame row C ∨
                  hsame row modulusRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont M R depthRead ∧ Cont depthRead Q modulusRead ∧
                  Cont Q H C ∧ Cont C P N)
              hsame ∧
            UnaryHistory depthRead ∧ UnaryHistory modulusRead ∧ hsame H (append Z S) ∧
              Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet depthRoute modulusRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have depthUnary : UnaryHistory depthRead :=
    unary_cont_closed unaryM unaryR depthRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed depthUnary unaryQ modulusRoute
  have sourceAtModulus : hsame modulusRead modulusRead ∧ UnaryHistory modulusRead :=
    ⟨hsame_refl modulusRead, modulusUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row Q ∨ hsame row H ∨ hsame row C ∨
              hsame row modulusRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M R depthRead ∧ Cont depthRead Q modulusRead ∧
              Cont Q H C ∧ Cont C P N)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro modulusRead sourceAtModulus
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, depthRoute, modulusRoute, routeC, routeN⟩
  }
  exact ⟨cert, depthUnary, modulusUnary, sameH, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
