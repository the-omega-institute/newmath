import BEDC.Derived.RealUp.FiniteWindow

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.Derived.RatUp

theorem RealStreamWindowClassifier_stability_package
    {x x' y y' z : Nat -> BHist} {n m : Nat} :
    ((forall k : Nat, k <= m -> RatHistoryCarrier (x (n + k))) ->
      RealStreamWindowClassifier x x n m) ∧
    (RealStreamWindowClassifier x y n m -> RealStreamWindowClassifier y x n m) ∧
    (RealStreamWindowClassifier x y n m -> RealStreamWindowClassifier y z n m ->
      RealStreamWindowClassifier x z n m) ∧
    (RealStreamWindowClassifier x y n m ->
      (forall k : Nat, k <= m ->
        hsame (x (n + k)) (x' (n + k)) ∧ hsame (y (n + k)) (y' (n + k))) ->
      RealStreamWindowClassifier x' y' n m) := by
  constructor
  · intro carrierX k windowBound
    exact ⟨carrierX k windowBound, carrierX k windowBound, hsame_refl (x (n + k))⟩
  constructor
  · intro classified k windowBound
    exact RatHistoryClassifier_symm (classified k windowBound)
  constructor
  · intro classifiedXY classifiedYZ k windowBound
    exact RatHistoryClassifier_trans (classifiedXY k windowBound)
      (classifiedYZ k windowBound)
  · intro classifiedXY transported k windowBound
    have sameRows := transported k windowBound
    exact RatHistoryClassifier_hsame_transport sameRows.left sameRows.right
      (classifiedXY k windowBound)

end BEDC.Derived.RealUp
