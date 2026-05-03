import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CategoryHomCarrier_tail_comm_hsame_congr {a a' b b' c c' f f' g g' fg gf : BHist} :
    hsame a a' -> hsame b b' -> hsame c c' -> hsame f f' -> hsame g g' ->
      CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f' g' fg ->
        Cont g' f' gf -> hsame fg gf := by
  intro sameA sameB sameC sameF sameG left right fgRel gfRel
  have movedLeft : CategoryHomCarrier a' b' f' :=
    CategoryHomCarrier_hsame_transport sameA sameB sameF left
  have movedRight : CategoryHomCarrier b' c' g' :=
    CategoryHomCarrier_hsame_transport sameB sameC sameG right
  exact CategoryHomCarrier_tail_comm_hsame movedLeft movedRight fgRel gfRel

end BEDC.Derived.CategoryUp
