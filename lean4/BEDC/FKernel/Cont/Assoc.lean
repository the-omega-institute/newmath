import BEDC.FKernel.Cont

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

theorem cont_assoc_up_to_hsame_spine {a b c ab bc left right : BHist} :
    Cont a b ab -> Cont ab c left -> Cont b c bc -> Cont a bc right -> hsame left right := by
  exact cont_assoc_hsame

theorem cont_assoc_proof_standing {a b c ab bc left right : BHist} :
    Cont a b ab -> Cont ab c left -> Cont b c bc -> Cont a bc right -> hsame left right := by
  intro hab hleft hbc hright
  cases hab
  cases hleft
  cases hbc
  cases hright
  exact append_assoc a b c

end BEDC.FKernel.Cont
