import BEDC.FKernel.Cont

namespace BEDC.FKernel.Cont

open BEDC.FKernel.Hist

theorem continuation_pattern_stability_fields :
    (forall h : BHist, Cont BHist.Empty h h) ∧
      (forall h : BHist, Cont h BHist.Empty h) ∧
        (forall {h k r r' : BHist}, Cont h k r -> Cont h k r' -> hsame r r') ∧
          (forall {a b c ab bc left right : BHist}, Cont a b ab -> Cont ab c left ->
            Cont b c bc -> Cont a bc right -> hsame left right) := by
  constructor
  · exact cont_left_unit
  · constructor
    · exact cont_right_unit
    · constructor
      · intro h k r r' left right
        exact cont_deterministic left right
      · intro a b c ab bc left right hab hleft hbc hright
        exact cont_assoc_hsame hab hleft hbc hright

theorem continuation_addition_like_seed_has_unit_assoc :
    (forall h : BHist, Cont BHist.Empty h h) ∧
      (forall h : BHist, Cont h BHist.Empty h) ∧
        (forall {a b c ab bc left right : BHist}, Cont a b ab -> Cont ab c left ->
          Cont b c bc -> Cont a bc right -> hsame left right) := by
  constructor
  · exact cont_left_unit
  · constructor
    · exact cont_right_unit
    · intro a b c ab bc left right hab hleft hbc hright
      exact cont_assoc_hsame hab hleft hbc hright

end BEDC.FKernel.Cont
