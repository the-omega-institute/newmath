import BEDC.Derived.MaxRateReadGateUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.MaxRateReadGateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem MaxRateReadGateNameCertObligations
    {M R S F L H Q C P N rateRead symmetryRead publicRead : BHist} :
    UnaryHistory M →
      UnaryHistory R →
        UnaryHistory S →
          UnaryHistory F →
            UnaryHistory L →
              Cont M R rateRead →
                Cont rateRead S symmetryRead →
                  Cont symmetryRead F publicRead →
                    hsame H Q →
                      hsame P N →
                        SemanticNameCert
                              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row M ∨ hsame row R ∨ hsame row S ∨ hsame row F ∨
                                  hsame row L ∨ hsame row H ∨ hsame row Q ∨ hsame row C ∨
                                    hsame row P ∨ hsame row N ∨ hsame row publicRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont M R rateRead ∧
                                  Cont rateRead S symmetryRead ∧
                                    Cont symmetryRead F publicRead ∧ hsame H Q ∧ hsame P N)
                              hsame ∧
                          UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro unaryM unaryR unaryS unaryF _unaryL rateRoute symmetryRoute publicRoute sameHQ
    samePN
  have rateUnary : UnaryHistory rateRead :=
    unary_cont_closed unaryM unaryR rateRoute
  have symmetryUnary : UnaryHistory symmetryRead :=
    unary_cont_closed rateUnary unaryS symmetryRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed symmetryUnary unaryF publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row S ∨ hsame row F ∨ hsame row L ∨
              hsame row H ∨ hsame row Q ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M R rateRead ∧ Cont rateRead S symmetryRead ∧
              Cont symmetryRead F publicRead ∧ hsame H Q ∧ hsame P N)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, rateRoute, symmetryRoute, publicRoute, sameHQ, samePN⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.MaxRateReadGateUp
