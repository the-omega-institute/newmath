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

theorem ZeckendorfCarryNormalizationCarrier_boundary_transport [AskSetup] [PackageSetup]
    {source target carryRoute valueLedger boundary routes provenance name source' target'
      carryRoute' valueLedger' boundary' routes' provenance' name' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZeckendorfCarryNormalizationCarrier source target carryRoute valueLedger boundary routes
      provenance name bundle pkg ->
    hsame source source' ->
    hsame target target' ->
    hsame carryRoute carryRoute' ->
    hsame valueLedger valueLedger' ->
    hsame boundary boundary' ->
    hsame routes routes' ->
    hsame provenance provenance' ->
    hsame name name' ->
    Cont source' target' carryRoute' ->
    Cont carryRoute' valueLedger' routes' ->
    PkgSig bundle provenance' pkg ->
    PkgSig bundle name' pkg ->
      ZeckendorfCarryNormalizationCarrier source' target' carryRoute' valueLedger' boundary'
        routes' provenance' name' bundle pkg ∧ ¬ hsame source' target' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig ZCarry ZNormal
  intro carrier sameSource sameTarget sameCarryRoute sameValueLedger sameBoundary sameRoutes
    sameProvenance sameName sourceTargetCarry' carryLedgerRoute' provenancePkg' namePkg'
  obtain ⟨sourceTargetCarry, targetNormal, sourceNotNormal, sourceNotTarget,
    _sourceTargetRoute, _carryLedgerRoute, _provenancePkg, _namePkg⟩ := carrier
  cases sameSource
  cases sameTarget
  cases sameCarryRoute
  cases sameValueLedger
  cases sameBoundary
  cases sameRoutes
  cases sameProvenance
  cases sameName
  exact
    ⟨⟨sourceTargetCarry, targetNormal, sourceNotNormal, sourceNotTarget,
        sourceTargetCarry', carryLedgerRoute', provenancePkg', namePkg'⟩,
      sourceNotTarget⟩

theorem ZeckendorfCarryNormalizationCarrier_value_ledger [AskSetup] [PackageSetup]
    {source target carryRoute valueLedger boundary routes provenance name ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZeckendorfCarryNormalizationCarrier source target carryRoute valueLedger boundary routes
        provenance name bundle pkg →
      Cont carryRoute valueLedger ledgerRead →
        PkgSig bundle ledgerRead pkg →
          ZCarry source target ∧ ¬ ZNormal source ∧ ¬ hsame source target ∧
            Cont source target carryRoute ∧ Cont carryRoute valueLedger routes ∧
              Cont carryRoute valueLedger ledgerRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig ZCarry ZNormal
  intro carrier carryLedgerRead ledgerReadPkg
  obtain ⟨sourceTargetCarry, _targetNormal, sourceNotNormal, sourceNotTarget,
    sourceTargetRoute, carryLedgerRoute, provenancePkg, _namePkg⟩ := carrier
  exact
    ⟨sourceTargetCarry, sourceNotNormal, sourceNotTarget, sourceTargetRoute,
      carryLedgerRoute, carryLedgerRead, provenancePkg, ledgerReadPkg⟩

end BEDC.Derived.ZeckendorfCarryNormalizationUp
