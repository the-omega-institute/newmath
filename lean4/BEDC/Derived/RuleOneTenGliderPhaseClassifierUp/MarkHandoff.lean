import BEDC.Derived.RuleOneTenGliderPhaseClassifierUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.RuleOneTenGliderPhaseClassifierUp.TasteGate

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem RuleOneTenGliderPhaseClassifierCarrier_mark_handoff
    {R W K O M E L H C P N catalogRead phaseRead localRead exposureRead : BHist} :
    Cont R W catalogRead →
      Cont catalogRead K phaseRead →
        Cont phaseRead O localRead →
          Cont localRead M exposureRead →
            ruleOneTenGliderPhaseClassifierFromEventFlow
                (ruleOneTenGliderPhaseClassifierToEventFlow
                  (RuleOneTenGliderPhaseClassifierUp.mk R W K O M E L H C P N)) =
              some (RuleOneTenGliderPhaseClassifierUp.mk R W K O M E L H C P N) ∧
              Cont catalogRead K phaseRead ∧
                Cont phaseRead O localRead ∧
                  Cont localRead M exposureRead ∧
                    List.Mem (ruleOneTenGliderPhaseClassifierEncodeBHist O)
                      (ruleOneTenGliderPhaseClassifierToEventFlow
                        (RuleOneTenGliderPhaseClassifierUp.mk R W K O M E L H C P N)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont
  intro _catalogCont phaseCont localCont exposureCont
  have decode :
      ∀ h : BHist,
        ruleOneTenGliderPhaseClassifierDecodeBHist
          (ruleOneTenGliderPhaseClassifierEncodeBHist h) = h :=
    RuleOneTenGliderPhaseClassifierTasteGate_single_carrier_alignment.left
  constructor
  · change
      some
          (RuleOneTenGliderPhaseClassifierUp.mk
            (ruleOneTenGliderPhaseClassifierDecodeBHist
              (ruleOneTenGliderPhaseClassifierEncodeBHist R))
            (ruleOneTenGliderPhaseClassifierDecodeBHist
              (ruleOneTenGliderPhaseClassifierEncodeBHist W))
            (ruleOneTenGliderPhaseClassifierDecodeBHist
              (ruleOneTenGliderPhaseClassifierEncodeBHist K))
            (ruleOneTenGliderPhaseClassifierDecodeBHist
              (ruleOneTenGliderPhaseClassifierEncodeBHist O))
            (ruleOneTenGliderPhaseClassifierDecodeBHist
              (ruleOneTenGliderPhaseClassifierEncodeBHist M))
            (ruleOneTenGliderPhaseClassifierDecodeBHist
              (ruleOneTenGliderPhaseClassifierEncodeBHist E))
            (ruleOneTenGliderPhaseClassifierDecodeBHist
              (ruleOneTenGliderPhaseClassifierEncodeBHist L))
            (ruleOneTenGliderPhaseClassifierDecodeBHist
              (ruleOneTenGliderPhaseClassifierEncodeBHist H))
            (ruleOneTenGliderPhaseClassifierDecodeBHist
              (ruleOneTenGliderPhaseClassifierEncodeBHist C))
            (ruleOneTenGliderPhaseClassifierDecodeBHist
              (ruleOneTenGliderPhaseClassifierEncodeBHist P))
            (ruleOneTenGliderPhaseClassifierDecodeBHist
              (ruleOneTenGliderPhaseClassifierEncodeBHist N))) =
        some (RuleOneTenGliderPhaseClassifierUp.mk R W K O M E L H C P N)
    rw [decode R, decode W, decode K, decode O, decode M, decode E, decode L, decode H,
      decode C, decode P, decode N]
  · constructor
    · exact phaseCont
    · constructor
      · exact localCont
      · constructor
        · exact exposureCont
        · simp only [ruleOneTenGliderPhaseClassifierToEventFlow]
          right
          right
          right
          right
          right
          right
          right
          left

end BEDC.Derived.RuleOneTenGliderPhaseClassifierUp.TasteGate
