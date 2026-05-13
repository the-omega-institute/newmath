import BEDC.Derived.AxisZeckendorf.Carry
import BEDC.FKernel.Cont

namespace BEDC.Derived.ZCarryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.AxisZeckendorf.Zeckendorf
open BEDC.Derived.AxisZeckendorf.Carry

structure ZCarryFiniteCarryPacket : Type where
  source : BHist
  target : BHist
  carryRoute : BHist
  generated : ZCarry source target
  sourceNotNormal : ZCarrySourceSpec source
  targetNormal : ZNormal target
  nonHsame : ¬ hsame source target
  sourceReadback : Cont source BHist.Empty source
  targetReadback : Cont target BHist.Empty target
  carryReadback : Cont source target carryRoute
  namecert : ZCarryNameCert

theorem ZCarryFiniteCarryPacket_obligation_surface (Z : ZCarryFiniteCarryPacket) :
    Z.source = word_011 ∧ Z.target = word_100 ∧
      ZCarry Z.source Z.target ∧ ZCarrySourceSpec Z.source ∧
        ZNormal Z.target ∧ ¬ hsame Z.source Z.target ∧
          ZCarryClassifierSpec Z.source Z.target ∧
            ZCarryLedgerPolicy Z.source Z.target ∧
              Cont Z.source Z.target Z.carryRoute := by
  cases Z with
  | mk source target carryRoute generated sourceNotNormal targetNormal nonHsame
      sourceReadback targetReadback carryReadback namecert =>
      cases generated with
      | base =>
          constructor
          · rfl
          · constructor
            · rfl
            · constructor
              · exact ZCarry.base
              · constructor
                · exact sourceNotNormal
                · constructor
                  · exact targetNormal
                  · constructor
                    · exact nonHsame
                    · constructor
                      · exact And.intro ZCarry.base
                          (And.intro targetNormal
                            (And.intro sourceNotNormal nonHsame))
                      · exact And.intro ZCarry.base carryReadback

end BEDC.Derived.ZCarryUp
