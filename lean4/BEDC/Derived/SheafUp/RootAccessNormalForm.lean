import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SheafRootAccessNormalForm_consumer_factorization
    {root h k : BHist} {landing : SheafRootFaceLanding} {trace : List BHist} :
    SheafConsumerAccessTrace root trace -> List.Mem h trace ->
      SheafRootFaceRead h k landing ->
        UnaryHistory root ∧ UnaryHistory h ∧
          ((landing = SheafRootFaceLanding.coverMembership ∧ hsame h k) ∨
            (landing = SheafRootFaceLanding.restrictionRoute ∧
              (hsame h k ∨ ∃ sectionHist : BHist, Cont h sectionHist k)) ∨
              (landing = SheafRootFaceLanding.localityGluingRefinement ∧
                ∃ sectA : BHist, ∃ sectB : BHist, ∃ germB : BHist,
                  Cont h sectA k ∧ Cont h sectB germB ∧ hsame k germB)) := by
  intro consumer hMem read
  have hUnary : UnaryHistory h :=
    consumer.right h hMem
  cases read with
  | carrierClassifier sameHK =>
      exact And.intro consumer.left
        (And.intro hUnary
          (Or.inr
            (Or.inl
              (And.intro rfl (Or.inl sameHK)))))
  | restrictionRoute route =>
      exact And.intro consumer.left
        (And.intro hUnary
          (Or.inr
            (Or.inl
              (And.intro rfl (Or.inr (Exists.intro _ route))))))
  | coverMembership sameHK =>
      exact And.intro consumer.left
        (And.intro hUnary
          (Or.inl (And.intro rfl sameHK)))
  | localityGluingRefinement routeA routeB sameGerms =>
      exact And.intro consumer.left
        (And.intro hUnary
          (Or.inr
            (Or.inr
              (And.intro rfl
                (Exists.intro _
                  (Exists.intro _
                    (Exists.intro _
                      (And.intro routeA (And.intro routeB sameGerms)))))))))

end BEDC.Derived.SheafUp
