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

theorem ZeckendorfCarryNormalizationCarrier_source_target_totality [AskSetup] [PackageSetup]
    {source target carryRoute valueLedger boundary routes provenance name sourceRead
      targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZeckendorfCarryNormalizationCarrier source target carryRoute valueLedger boundary routes
        provenance name bundle pkg →
      Cont source carryRoute sourceRead →
        Cont target carryRoute targetRead →
          PkgSig bundle sourceRead pkg →
            PkgSig bundle targetRead pkg →
              ZCarry source target ∧ ¬ ZNormal source ∧ ZNormal target ∧
                ¬ hsame source target ∧ Cont source target carryRoute ∧
                  Cont source carryRoute sourceRead ∧ Cont target carryRoute targetRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle sourceRead pkg ∧ PkgSig bundle targetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig ZCarry ZNormal
  intro carrier sourceCarryRead targetCarryRead sourceReadPkg targetReadPkg
  obtain ⟨sourceTargetCarry, targetNormal, sourceNotNormal, sourceNotTarget,
    sourceTargetRoute, _carryLedgerRoute, provenancePkg, namePkg⟩ := carrier
  exact
    ⟨sourceTargetCarry, sourceNotNormal, targetNormal, sourceNotTarget, sourceTargetRoute,
      sourceCarryRead, targetCarryRead, provenancePkg, namePkg, sourceReadPkg,
      targetReadPkg⟩

theorem ZeckendorfCarryNormalizationCarrier_source_target_window_totality [AskSetup]
    [PackageSetup] {source target carryRoute valueLedger boundary routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZeckendorfCarryNormalizationCarrier source target carryRoute valueLedger boundary routes
        provenance name bundle pkg →
      source = word_011 ∧ target = word_100 ∧ ZCarry source target ∧ ZNormal target ∧
        ¬ ZNormal source ∧ ¬ hsame source target ∧ Cont source target carryRoute ∧
          Cont carryRoute valueLedger routes ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig ZCarry ZNormal
  intro carrier
  obtain ⟨sourceTargetCarry, targetNormal, sourceNotNormal, sourceNotTarget,
    sourceTargetRoute, carryLedgerRoute, provenancePkg, namePkg⟩ := carrier
  obtain ⟨sourceWindow, targetWindow, _sourceWindowNotNormal, _targetWindowNormal,
    _sourceWindowNotTarget⟩ := ZCarry_window_determinacy sourceTargetCarry
  exact
    ⟨sourceWindow, targetWindow, sourceTargetCarry, targetNormal, sourceNotNormal,
      sourceNotTarget, sourceTargetRoute, carryLedgerRoute, provenancePkg, namePkg⟩

theorem ZeckendorfCarryNormalizationCarrier_local_name_window_exhaustion [AskSetup]
    [PackageSetup] {source target carryRoute valueLedger boundary routes provenance name
      nameRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZeckendorfCarryNormalizationCarrier source target carryRoute valueLedger boundary routes
        provenance name bundle pkg →
      Cont provenance name nameRead →
        PkgSig bundle nameRead pkg →
          source = word_011 ∧ target = word_100 ∧ ZCarry source target ∧
            ZNormal target ∧ ¬ ZNormal source ∧ ¬ hsame source target ∧
              Cont provenance name nameRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle name pkg ∧ PkgSig bundle nameRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig ZCarry ZNormal
  intro carrier provenanceNameRead nameReadPkg
  obtain ⟨sourceTargetCarry, targetNormal, sourceNotNormal, sourceNotTarget,
    _sourceTargetRoute, _carryLedgerRoute, provenancePkg, namePkg⟩ := carrier
  obtain ⟨sourceWindow, targetWindow, _sourceWindowNotNormal, _targetWindowNormal,
    _sourceWindowNotTarget⟩ := ZCarry_window_determinacy sourceTargetCarry
  exact
    ⟨sourceWindow, targetWindow, sourceTargetCarry, targetNormal, sourceNotNormal,
      sourceNotTarget, provenanceNameRead, provenancePkg, namePkg, nameReadPkg⟩

end BEDC.Derived.ZeckendorfCarryNormalizationUp
