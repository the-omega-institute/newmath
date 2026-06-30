import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_gap_policy_stability
    {Z S M R Q H C P N gapRead policyRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S gapRead ->
        Cont gapRead Q policyRead ->
          SemanticNameCert
              (fun row : BHist => hsame row policyRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
                  hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                    hsame row gapRead ∨ hsame row policyRead)
              (fun row : BHist =>
                hsame row policyRead ∧ Cont Z S gapRead ∧ Cont gapRead Q policyRead)
              hsame ∧
            UnaryHistory gapRead ∧ UnaryHistory policyRead ∧ hsame H (append Z S) ∧
              Cont Z S gapRead ∧ Cont gapRead Q policyRead ∧ Cont M R Q ∧
                Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet gapRoute policyRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have gapUnary : UnaryHistory gapRead :=
    unary_cont_closed unaryZ unaryS gapRoute
  have policyUnary : UnaryHistory policyRead :=
    unary_cont_closed gapUnary unaryQ policyRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row policyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row gapRead ∨ hsame row policyRead)
          (fun row : BHist =>
            hsame row policyRead ∧ Cont Z S gapRead ∧ Cont gapRead Q policyRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro policyRead
        ⟨hsame_refl policyRead, policyUnary⟩
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
      exact ⟨source.left, gapRoute, policyRoute⟩
  }
  exact
    ⟨cert, gapUnary, policyUnary, sameH, gapRoute, policyRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
