import BEDC.FKernel.Cont.AssocSpine

namespace BEDC.FKernel.Cont

open BEDC.FKernel.Hist

theorem cont_assoc_common_witness {a b c ab bc left right : BHist} :
    Cont a b ab → Cont b c bc → Cont ab c left → Cont a bc right →
      ∃ common : BHist,
        Cont ab c common ∧ Cont a bc common ∧ hsame left common ∧ hsame right common := by
  intro hab hbc hleft hright
  cases cont_assoc_exists hab hbc with
  | intro common commonData =>
      cases commonData with
      | intro hleftCommon hrightCommon =>
          have hleftSame : hsame left common := cont_deterministic hleft hleftCommon
          have hrightSame : hsame right common := cont_deterministic hright hrightCommon
          exact ⟨common, hleftCommon, hrightCommon, hleftSame, hrightSame⟩

theorem cont_assoc_common_witness_symmetric {a b c ab bc left right : BHist} :
    Cont a b ab -> Cont b c bc -> Cont ab c left -> Cont a bc right ->
      exists common : BHist,
        Cont ab c common /\ Cont a bc common /\ hsame left common /\ hsame common left /\
          hsame right common /\ hsame common right := by
  intro hab hbc hleft hright
  cases cont_assoc_common_witness hab hbc hleft hright with
  | intro common data =>
      exact ⟨common, data.left, data.right.left, data.right.right.left,
        hsame_symm data.right.right.left, data.right.right.right,
        hsame_symm data.right.right.right⟩

theorem cont_assoc_up_to_hsame_spine {a b c ab bc left right : BHist} :
    Cont a b ab -> Cont ab c left -> Cont b c bc -> Cont a bc right -> hsame left right := by
  exact cont_assoc_hsame

theorem cont_right_append_decompose {h k l r : BHist} :
    Cont h (append k l) r -> exists mid : BHist, Cont h k mid /\ Cont mid l r := by
  intro hcont
  cases hcont
  exact ⟨append h k, rfl, (append_assoc h k l).symm⟩

theorem cont_assoc_five {a b c d e ab abc abcd de cde bcde left right : BHist} :
    Cont a b ab → Cont ab c abc → Cont abc d abcd → Cont d e de → Cont c de cde →
      Cont b cde bcde → Cont abcd e left → Cont a bcde right → hsame left right := by
  intro hab habc habcd hde hcde hbcde hleft hright
  cases hab
  cases habc
  cases habcd
  cases hde
  cases hcde
  cases hbcde
  cases hleft
  cases hright
  exact (append_assoc (append (append a b) c) d e).trans
    ((append_assoc (append a b) c (append d e)).trans
      (append_assoc a b (append c (append d e))))

theorem cont_assoc_six {a b c d e f ab abc abcd abcde ef «def» cdef bcdef left right : BHist} :
    Cont a b ab -> Cont ab c abc -> Cont abc d abcd -> Cont abcd e abcde ->
      Cont e f ef -> Cont d ef «def» -> Cont c «def» cdef -> Cont b cdef bcdef ->
      Cont abcde f left -> Cont a bcdef right -> hsame left right := by
  intro hab habc habcd habcde hef hdef hcdef hbcdef hleft hright
  cases hab
  cases habc
  cases habcd
  cases habcde
  cases hef
  cases hdef
  cases hcdef
  cases hbcdef
  cases hleft
  cases hright
  exact (append_assoc (append (append (append a b) c) d) e f).trans
    ((append_assoc (append (append a b) c) d (append e f)).trans
      ((append_assoc (append a b) c (append d (append e f))).trans
        (append_assoc a b (append c (append d (append e f))))))

end BEDC.FKernel.Cont
