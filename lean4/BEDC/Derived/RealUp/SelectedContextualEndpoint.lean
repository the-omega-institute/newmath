import BEDC.Derived.RealUp.PrefixTruncation

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RealStreamClassifier_selected_contextual_full_endpoint_package
    {x y prefX prefY tailX tailY midX midY outX outY : Nat -> BHist} {n : Nat}
    {leftTail rightTail zX zY : BHist} :
    RealStreamClassifier x y -> UnaryHistory (prefX n) ->
      UnaryHistory (tailX n) -> hsame (prefX n) (prefY n) ->
        hsame (tailX n) (tailY n) -> Cont (prefX n) (x n) (midX n) ->
          Cont (midX n) (tailX n) (outX n) -> Cont (prefY n) (y n) (midY n) ->
            Cont (midY n) (tailY n) (outY n) ->
              hsame (outX n) (BHist.e1 leftTail) ->
                hsame (outY n) (BHist.e1 rightTail) ->
                  RatHistoryClassifier (outX n) (outY n) ∧
                    PositiveUnaryDenominator (outX n) ∧ PositiveUnaryDenominator (outY n) ∧
                      UnaryHistory (outX n) ∧ UnaryHistory (outY n) ∧
                        (hsame (outX n) BHist.Empty -> False) ∧
                          (hsame (outY n) BHist.Empty -> False) ∧
                            (hsame (outX n) (BHist.e0 zX) -> False) ∧
                              (hsame (outY n) (BHist.e0 zY) -> False) ∧
                                UnaryHistory leftTail ∧ UnaryHistory rightTail ∧
                                  hsame leftTail rightTail := by
  intro classified prefUnary tailUnary prefSame tailSame prefCont outXCont prefYCont
    outYCont outXOne outYOne
  have prefixClassified : RealStreamPrefixClassifier x y (0 + n) := by
    simp only [Nat.zero_add]
    exact RealStreamClassifier_prefix classified n
  exact RealStreamPrefixClassifier_contextual_full_endpoint_package
    (m := 0) (n := n) prefixClassified prefUnary tailUnary prefSame tailSame prefCont
    outXCont prefYCont outYCont outXOne outYOne

end BEDC.Derived.RealUp
