import BEDC.Derived.RealUp.Core

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RealStreamClassifier_transport_selected_e1_pair_readback
    {x x' y y' : Nat -> BHist} {n : Nat} {a b : BHist} :
    (forall i : Nat, hsame (x i) (x' i)) ->
      (forall i : Nat, hsame (y i) (y' i)) ->
        RealStreamClassifier x y ->
          hsame (x' n) (BHist.e1 a) ->
            hsame (y' n) (BHist.e1 b) ->
              UnaryHistory a ∧ UnaryHistory b ∧ hsame a b := by
  intro sameX sameY classified sameLeft sameRight
  have hPrefix : RealStreamPrefixClassifier x y n :=
    (RealStreamClassifier_finite_prefix_exactness.mp classified) n
  have transported : RealStreamPrefixClassifier x' y' n :=
    RealStreamPrefixClassifier_hsame_transport sameX sameY n hPrefix
  exact RealStreamPrefixClassifier_e1_pair_readback transported sameLeft sameRight

end BEDC.Derived.RealUp
