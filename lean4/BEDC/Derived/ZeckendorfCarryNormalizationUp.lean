import BEDC.Derived.AxisZeckendorf.Carry
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package

namespace BEDC.Derived.ZeckendorfCarryNormalizationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.Derived.AxisZeckendorf.Carry
open BEDC.Derived.AxisZeckendorf.Zeckendorf

def ZeckendorfCarryNormalizationCarrier [AskSetup] [PackageSetup]
    (source target carryRoute valueLedger boundary routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig
  ZCarry source target ∧ ZNormal target ∧ ¬ ZNormal source ∧ ¬ hsame source target ∧
    Cont source target carryRoute ∧ Cont carryRoute valueLedger routes ∧
      PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem ZeckendorfCarryNormalizationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source target carryRoute valueLedger boundary routes provenance name valueRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZeckendorfCarryNormalizationCarrier source target carryRoute valueLedger boundary routes
      provenance name bundle pkg ->
    Cont routes valueLedger valueRead ->
    PkgSig bundle valueRead pkg ->
      ZCarry source target ∧ ZNormal target ∧ ¬ ZNormal source ∧ ¬ hsame source target ∧
        Cont source target carryRoute ∧ Cont carryRoute valueLedger routes ∧
          Cont routes valueLedger valueRead ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle name pkg ∧ PkgSig bundle valueRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig ZCarry ZNormal
  intro carrier valueReadRoute valueReadPkg
  obtain ⟨sourceTargetCarry, targetNormal, sourceNotNormal, sourceNotTarget,
    sourceTargetRoute, carryLedgerRoute, provenancePkg, namePkg⟩ := carrier
  exact
    ⟨sourceTargetCarry, targetNormal, sourceNotNormal, sourceNotTarget, sourceTargetRoute,
      carryLedgerRoute, valueReadRoute, provenancePkg, namePkg, valueReadPkg⟩

end BEDC.Derived.ZeckendorfCarryNormalizationUp
