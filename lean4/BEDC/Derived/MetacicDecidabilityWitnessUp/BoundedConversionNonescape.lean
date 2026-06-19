import BEDC.FKernel.Unary.History
import BEDC.Derived.MetacicDecidabilityWitnessUp.TasteGate

namespace BEDC.Derived.MetacicDecidabilityWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem MetacicDecidabilityWitnessCarrier_bounded_conversion_nonescape
    {B F R H C P N conversionRead boundedRead : BHist} :
    UnaryHistory B →
      UnaryHistory F →
        UnaryHistory R →
          hsame H (append B F) →
            Cont B F conversionRead →
              Cont conversionRead R boundedRead →
                Cont C P N →
                  UnaryHistory conversionRead ∧
                    UnaryHistory boundedRead ∧
                      hsame H (append B F) ∧
                        Cont B F conversionRead ∧
                          Cont conversionRead R boundedRead ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  intro hB hF hR hH hConversion hBounded hRoute
  constructor
  · exact unary_cont_closed hB hF hConversion
  · constructor
    · exact unary_cont_closed (unary_cont_closed hB hF hConversion) hR hBounded
    · constructor
      · exact hH
      · constructor
        · exact hConversion
        · constructor
          · exact hBounded
          · exact hRoute

end BEDC.Derived.MetacicDecidabilityWitnessUp
