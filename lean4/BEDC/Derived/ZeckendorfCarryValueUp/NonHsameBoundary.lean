import BEDC.Derived.AxisZeckendorf.Carry
import BEDC.Derived.ZeckendorfCarryValueUp.TasteGate

namespace BEDC.Derived.ZeckendorfCarryValueUp

open BEDC.FKernel.Hist
open BEDC.Derived.AxisZeckendorf.Carry
open BEDC.Derived.AxisZeckendorf.Zeckendorf

theorem ZeckendorfCarryValueNonHsameBoundary
    {source target carry sourceNormal targetNormal valueRow boundary route provenance nameCert :
      BHist} :
    ZCarry source target →
      ∃ packet : ZeckendorfCarryValueUp,
        packet =
            ZeckendorfCarryValueUp.mk source target carry sourceNormal targetNormal valueRow
              boundary route provenance nameCert ∧
          source = word_011 ∧ target = word_100 ∧ ¬ hsame source target ∧
            ¬ ZNormal source ∧ ZNormal target := by
  -- BEDC touchpoint anchor: BHist hsame ZCarry ZNormal
  intro sourceTargetCarry
  obtain ⟨sourceWindow, targetWindow, sourceNotNormal, targetNormalProof,
    sourceNotTarget⟩ := ZCarry_window_determinacy sourceTargetCarry
  exact
    ⟨ZeckendorfCarryValueUp.mk source target carry sourceNormal targetNormal valueRow
        boundary route provenance nameCert,
      rfl, sourceWindow, targetWindow, sourceNotTarget, sourceNotNormal, targetNormalProof⟩

end BEDC.Derived.ZeckendorfCarryValueUp
