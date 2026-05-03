import BEDC.Derived.CompactUp

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CompactNetWitness_left_e1_result_cases {center precision net : BHist} :
    CompactNetWitness (BHist.e1 center) precision (BHist.e1 net) ->
      (precision = BHist.Empty ∧ UnaryHistory center ∧ hsame center net) ∨
        (∃ precisionTail : BHist,
          precision = BHist.e1 precisionTail ∧
            CompactNetWitness (BHist.e1 center) precisionTail net) := by
  intro witness
  cases witness with
  | intro centerCarrier rest =>
      cases rest with
      | intro precisionCarrier rest =>
          cases rest with
          | intro netCarrier netRel =>
              have resultCases := cont_e1_result_inversion netRel
              cases resultCases with
              | inl emptyCase =>
                  exact Or.inl
                    (And.intro emptyCase.left
                      (And.intro (unary_e1_inversion centerCarrier)
                        (hsame_e1_iff.mp emptyCase.right)))
              | inr visibleCase =>
                  cases visibleCase with
                  | intro precisionTail tailData =>
                      cases tailData with
                      | intro precisionEq tailRel =>
                          cases precisionEq
                          exact Or.inr
                            (Exists.intro precisionTail
                              (And.intro rfl
                                (And.intro centerCarrier
                                  (And.intro (unary_e1_inversion precisionCarrier)
                                    (And.intro (unary_e1_inversion netCarrier) tailRel)))))

end BEDC.Derived.CompactUp
