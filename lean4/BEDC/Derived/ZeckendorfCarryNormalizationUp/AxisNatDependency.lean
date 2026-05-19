import BEDC.Derived.ZeckendorfCarryNormalizationUp

namespace BEDC.Derived.ZeckendorfCarryNormalizationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.Derived.AxisZeckendorf.Carry
open BEDC.Derived.AxisZeckendorf.Zeckendorf

theorem ZeckendorfCarryNormalizationCarrier_axis_nat_dependency [AskSetup] [PackageSetup]
    {source target carryRoute valueLedger boundary routes provenance name natRead valueRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZeckendorfCarryNormalizationCarrier source target carryRoute valueLedger boundary routes
        provenance name bundle pkg →
      Cont source valueLedger natRead →
        Cont natRead valueLedger valueRead →
          PkgSig bundle valueRead pkg →
            ZCarry source target ∧ ¬ ZNormal source ∧ ZNormal target ∧
              ¬ hsame source target ∧ Cont source target carryRoute ∧
                Cont source valueLedger natRead ∧ Cont natRead valueLedger valueRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle valueRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig ZCarry ZNormal
  intro carrier sourceValueRead natValueRead valueReadPkg
  obtain ⟨sourceTargetCarry, targetNormal, sourceNotNormal, sourceNotTarget,
    sourceTargetRoute, _carryLedgerRoute, provenancePkg, _namePkg⟩ := carrier
  exact
    ⟨sourceTargetCarry, sourceNotNormal, targetNormal, sourceNotTarget, sourceTargetRoute,
      sourceValueRead, natValueRead, provenancePkg, valueReadPkg⟩

end BEDC.Derived.ZeckendorfCarryNormalizationUp
