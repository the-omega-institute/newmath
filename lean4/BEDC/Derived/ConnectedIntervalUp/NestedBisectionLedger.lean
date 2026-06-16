import BEDC.Derived.ConnectedIntervalUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ConnectedIntervalUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem ConnectedIntervalCarrier_nested_bisection_ledger
    {L R W B S T E H C P N nestedRead : BHist} :
    ConnectedIntervalCarrier L R W B S T E H C P N →
      Cont B S nestedRead →
        SemanticNameCert
            (fun row : BHist => hsame row nestedRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row L ∨ hsame row R ∨ hsame row W ∨ hsame row B ∨ hsame row S ∨
                hsame row T ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                  hsame row N ∨ hsame row nestedRead)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont L W B ∧ Cont B S nestedRead ∧ Cont B S T ∧
                Cont H C P)
            hsame ∧
          UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory nestedRead ∧ Cont B S T ∧
            Cont H C P := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier nestedRoute
  obtain ⟨unaryL, _unaryR, unaryW, unaryS, _unaryE, routeB, routeT, _routeN, routeP⟩ :=
    carrier
  have unaryB : UnaryHistory B :=
    unary_cont_closed unaryL unaryW routeB
  have nestedUnary : UnaryHistory nestedRead :=
    unary_cont_closed unaryB unaryS nestedRoute
  have sourceAtNested : hsame nestedRead nestedRead ∧ UnaryHistory nestedRead :=
    ⟨hsame_refl nestedRead, nestedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nestedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row R ∨ hsame row W ∨ hsame row B ∨ hsame row S ∨
              hsame row T ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row nestedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L W B ∧ Cont B S nestedRead ∧ Cont B S T ∧
              Cont H C P)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nestedRead sourceAtNested
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeB, nestedRoute, routeT, routeP⟩
  }
  exact ⟨cert, unaryB, unaryS, nestedUnary, routeT, routeP⟩

end BEDC.Derived.ConnectedIntervalUp
