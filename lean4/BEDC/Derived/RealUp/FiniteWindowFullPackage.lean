import BEDC.Derived.RealUp.FiniteWindow

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp
open BEDC.Derived.StreamNameUp

theorem RealUnaryStreamWindowClassifier_selected_canonical_e1_tail_full_package
    {s t : BHist -> BHist} {a w k zS zT dS dT : BHist} :
    RatStreamNameCarrier s -> RatStreamNameCarrier t -> RatStreamNameClassifier s t ->
      UnaryHistory a -> UnaryHistory w -> UnaryOffsetLe k w ->
        exists u : BHist, exists v : BHist,
          hsame (s (append a k)) (BHist.e1 u) ∧
            hsame (t (append a k)) (BHist.e1 v) ∧
              RealUnaryStreamWindowClassifier s t a w ∧
                RatHistoryClassifier (s (append a k)) (t (append a k)) ∧
                  RatHistoryClassifier (BHist.e1 u) (BHist.e1 v) ∧
                    UnaryHistory u ∧ UnaryHistory v ∧ hsame u v ∧
                      PositiveUnaryDenominator (s (append a k)) ∧
                        PositiveUnaryDenominator (t (append a k)) ∧
                          UnaryHistory (s (append a k)) ∧
                            UnaryHistory (t (append a k)) ∧
                              (hsame (s (append a k)) BHist.Empty -> False) ∧
                                (hsame (t (append a k)) BHist.Empty -> False) ∧
                                  (hsame (s (append a k)) (BHist.e0 zS) -> False) ∧
                                    (hsame (t (append a k)) (BHist.e0 zT) -> False) ∧
                                      (hsame (s (append a k))
                                          (append dS (BHist.e0 zS)) -> False) ∧
                                        (hsame (t (append a k))
                                          (append dT (BHist.e0 zT)) -> False) ∧
                                          forall u' v' : BHist,
                                            (hsame (s (append a k)) (BHist.e1 u') ∧
                                              hsame (t (append a k)) (BHist.e1 v')) ->
                                                UnaryHistory u' ∧ UnaryHistory v' ∧
                                                  hsame u u' ∧ hsame v v' ∧
                                                    hsame u' v ∧ hsame u v' := by
  intro carrierS carrierT classified aUnary wUnary offset
  have coverage :=
    RealUnaryStreamWindowClassifier_selected_e1_tail_coverage_package
      (s := s) (t := t) (a := a) (w := w) (k := k)
      (zS := zS) (zT := zT) (dS := dS) (dT := dT)
      carrierS carrierT classified aUnary wUnary offset
  cases coverage with
  | intro u coverageU =>
      cases coverageU with
      | intro v data =>
          exact ⟨u, v, data.left, data.right.left, data.right.right.left,
            data.right.right.right.left, data.right.right.right.right.left,
            data.right.right.right.right.right.left,
            data.right.right.right.right.right.right.left,
            data.right.right.right.right.right.right.right.left,
            data.right.right.right.right.right.right.right.right.left,
            data.right.right.right.right.right.right.right.right.right.left,
            data.right.right.right.right.right.right.right.right.right.right.left,
            data.right.right.right.right.right.right.right.right.right.right.right.left,
            data.right.right.right.right.right.right.right.right.right.right.right.right.left,
            data.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
            data.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
            data.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
            data.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
            data.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right,
            fun u' v' displayed =>
              have displayedClassifier :
                  RatHistoryClassifier (BHist.e1 u') (BHist.e1 v') :=
                RatHistoryClassifier_hsame_transport displayed.left displayed.right
                  data.right.right.right.left
              have displayedReadback :
                  UnaryHistory u' ∧ UnaryHistory v' ∧ hsame u' v' :=
                RatHistoryClassifier_e1_tail_unary_iff.mp displayedClassifier
              have sameUU' : hsame u u' :=
                hsame_e1_iff.mp (hsame_trans (hsame_symm data.left) displayed.left)
              have sameVV' : hsame v v' :=
                hsame_e1_iff.mp
                  (hsame_trans (hsame_symm data.right.left) displayed.right)
              have sameUV : hsame u v :=
                data.right.right.right.right.right.right.right.left
              ⟨displayedReadback.left, displayedReadback.right.left, sameUU', sameVV',
                hsame_trans (hsame_symm sameUU') sameUV, hsame_trans sameUV sameVV'⟩⟩

end BEDC.Derived.RealUp
