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

end BEDC.FKernel.Cont
