import BEDC.FKernel.Cont

namespace BEDC.Derived.ErrorCodeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

structure ErrorCodeMinimumDistanceInterface where
  code : BHist -> Prop
  classifier : BHist -> BHist -> Prop
  distance : BHist -> BHist -> Nat
  minimumDistance : Nat
  decodingRadius : Nat
  distance_symm : ∀ x y : BHist, distance x y = distance y x
  distance_triangle :
    ∀ x y z : BHist, distance x z <= distance x y + distance y z
  radius_double_lt_minimum : decodingRadius + decodingRadius < minimumDistance
  minimum_distance_classifier :
    ∀ {x y : BHist}, code x -> code y -> distance x y < minimumDistance -> classifier x y
  classifier_sound :
    ∀ {x y : BHist}, classifier x y -> hsame (append x BHist.Empty) y

theorem ErrorCodeMinimumDistanceInterface_unique_decoding_radius
    (C : ErrorCodeMinimumDistanceInterface) {c1 c2 r : BHist} :
    C.code c1 -> C.code c2 -> C.distance c1 r <= C.decodingRadius ->
      C.distance c2 r <= C.decodingRadius ->
        C.classifier c1 c2 ∧ hsame (append c1 BHist.Empty) c2 := by
  intro c1Code c2Code c1Radius c2Radius
  have rToC2Radius : C.distance r c2 <= C.decodingRadius := by
    rw [C.distance_symm r c2]
    exact c2Radius
  have combinedRadius :
      C.distance c1 r + C.distance r c2 <= C.decodingRadius + C.decodingRadius :=
    Nat.add_le_add c1Radius rToC2Radius
  have distanceBound : C.distance c1 c2 <= C.decodingRadius + C.decodingRadius :=
    Nat.le_trans (C.distance_triangle c1 r c2) combinedRadius
  have belowMinimum : C.distance c1 c2 < C.minimumDistance :=
    Nat.lt_of_le_of_lt distanceBound C.radius_double_lt_minimum
  have classified : C.classifier c1 c2 :=
    C.minimum_distance_classifier c1Code c2Code belowMinimum
  exact And.intro classified (C.classifier_sound classified)

end BEDC.Derived.ErrorCodeUp
