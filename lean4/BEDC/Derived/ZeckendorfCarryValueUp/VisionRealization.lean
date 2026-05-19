import BEDC.Derived.AxisZeckendorf.Carry
import BEDC.Derived.ZeckendorfCarryValueUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package

namespace BEDC.Derived.ZeckendorfCarryValueUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.Derived.AxisZeckendorf.Carry
open BEDC.Derived.AxisZeckendorf.Zeckendorf

theorem ZeckendorfCarryValueVisionRealization [AskSetup] [PackageSetup]
    {source target carry sourceNormal targetNormal valueRow boundary route provenance nameCert
      valueRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZCarry source target →
      Cont carry valueRow valueRead →
        Cont valueRead route publicRead →
          PkgSig bundle provenance pkg →
            PkgSig bundle publicRead pkg →
              Exists fun packet : ZeckendorfCarryValueUp =>
                packet =
                    ZeckendorfCarryValueUp.mk source target carry sourceNormal targetNormal
                      valueRow boundary route provenance nameCert ∧
                  source = word_011 ∧
                    target = word_100 ∧
                      Not (hsame source target) ∧
                        Cont carry valueRow valueRead ∧
                          Cont valueRead route publicRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame ZCarry
  intro sourceTargetCarry carryValueRoute valuePublicRoute provenancePkg publicPkg
  obtain ⟨sourceWindow, targetWindow, _sourceNotNormal, _targetNormalProof,
    sourceNotTarget⟩ := ZCarry_window_determinacy sourceTargetCarry
  exact
    ⟨ZeckendorfCarryValueUp.mk source target carry sourceNormal targetNormal valueRow
        boundary route provenance nameCert,
      rfl,
      sourceWindow,
      targetWindow,
      sourceNotTarget,
      carryValueRoute,
      valuePublicRoute,
      provenancePkg,
      publicPkg⟩

end BEDC.Derived.ZeckendorfCarryValueUp
