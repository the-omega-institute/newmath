import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SylowUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SylowCarrier [AskSetup] [PackageSetup]
    (groupRow subgroupRow primeRow exponentRow coverageRow actionRow transportRow consumerRow
      hsameRow provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig hsame
  UnaryHistory groupRow ∧ UnaryHistory subgroupRow ∧ UnaryHistory primeRow ∧
    UnaryHistory exponentRow ∧ UnaryHistory coverageRow ∧ UnaryHistory actionRow ∧
      UnaryHistory transportRow ∧ UnaryHistory consumerRow ∧ UnaryHistory hsameRow ∧
        UnaryHistory provenance ∧ UnaryHistory localCert ∧
          Cont groupRow subgroupRow coverageRow ∧ Cont coverageRow actionRow transportRow ∧
            Cont transportRow consumerRow hsameRow ∧ hsame consumerRow provenance ∧
              hsame hsameRow provenance ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle localCert pkg

theorem SylowCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {groupRow subgroupRow primeRow exponentRow coverageRow actionRow transportRow consumerRow
      hsameRow provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SylowCarrier groupRow subgroupRow primeRow exponentRow coverageRow actionRow transportRow
        consumerRow hsameRow provenance localCert bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row provenance ∧
              SylowCarrier groupRow subgroupRow primeRow exponentRow coverageRow actionRow
                transportRow consumerRow hsameRow provenance localCert bundle pkg)
          (fun row : BHist =>
            hsame row groupRow ∨ hsame row subgroupRow ∨ hsame row primeRow ∨
              hsame row exponentRow ∨ hsame row coverageRow ∨ hsame row actionRow ∨
                hsame row transportRow ∨ hsame row consumerRow)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory groupRow ∧ UnaryHistory subgroupRow ∧ UnaryHistory primeRow ∧
          UnaryHistory exponentRow ∧ UnaryHistory coverageRow ∧ UnaryHistory actionRow ∧
            UnaryHistory transportRow ∧ UnaryHistory consumerRow ∧
              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier
  have carrierPacket :
      SylowCarrier groupRow subgroupRow primeRow exponentRow coverageRow actionRow transportRow
        consumerRow hsameRow provenance localCert bundle pkg :=
    carrier
  obtain ⟨groupUnary, subgroupUnary, primeUnary, exponentUnary, coverageUnary, actionUnary,
    transportUnary, consumerUnary, _hsameUnary, _provenanceUnary, _localCertUnary,
    _coverageRoute, _transportRoute, _consumerRoute, sameConsumerProvenance,
    _sameHsameProvenance, provenancePkg, _localCertPkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row provenance ∧
              SylowCarrier groupRow subgroupRow primeRow exponentRow coverageRow actionRow
                transportRow consumerRow hsameRow provenance localCert bundle pkg)
          (fun row : BHist =>
            hsame row groupRow ∨ hsame row subgroupRow ∨ hsame row primeRow ∨
              hsame row exponentRow ∨ hsame row coverageRow ∨ hsame row actionRow ∨
                hsame row transportRow ∨ hsame row consumerRow)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          hsame := by
    have consumerPattern :
        hsame provenance groupRow ∨ hsame provenance subgroupRow ∨
          hsame provenance primeRow ∨ hsame provenance exponentRow ∨
            hsame provenance coverageRow ∨ hsame provenance actionRow ∨
              hsame provenance transportRow ∨ hsame provenance consumerRow := by
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (hsame_symm sameConsumerProvenance)))))))
    exact {
      core := {
        carrier_inhabited := Exists.intro provenance ⟨hsame_refl provenance, carrierPacket⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows sourceRow
          exact ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        cases sourceRow.left with
        | refl =>
            exact consumerPattern
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, provenancePkg⟩
    }
  exact
    ⟨cert, groupUnary, subgroupUnary, primeUnary, exponentUnary, coverageUnary, actionUnary,
      transportUnary, consumerUnary, provenancePkg⟩

theorem SylowCarrier_conjugacy_transport [AskSetup] [PackageSetup]
    {groupRow subgroupRow subgroupRow' primeRow exponentRow coverageRow coverageRow' actionRow
      actionRow' transportRow transportRow' consumerRow consumerRow' hsameRow hsameRow'
      provenance provenance' localCert localCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SylowCarrier groupRow subgroupRow primeRow exponentRow coverageRow actionRow transportRow
        consumerRow hsameRow provenance localCert bundle pkg →
      SylowCarrier groupRow subgroupRow' primeRow exponentRow coverageRow' actionRow'
          transportRow' consumerRow' hsameRow' provenance' localCert' bundle pkg →
        hsame coverageRow coverageRow' →
          hsame actionRow actionRow' →
            hsame transportRow transportRow' ∧ UnaryHistory transportRow ∧
              UnaryHistory transportRow' ∧ Cont coverageRow actionRow transportRow ∧
                Cont coverageRow' actionRow' transportRow' := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory Cont ProbeBundle Pkg
  intro carrier carrier' sameCoverage sameAction
  obtain ⟨_groupUnary, _subgroupUnary, _primeUnary, _exponentUnary, _coverageUnary,
    _actionUnary, transportUnary, _consumerUnary, _hsameUnary, _provenanceUnary,
    _localCertUnary, _coverageRoute, transportRoute, _consumerRoute,
    _sameConsumerProvenance, _sameHsameProvenance, _provenancePkg,
    _localCertPkg⟩ := carrier
  obtain ⟨_groupUnary', _subgroupUnary', _primeUnary', _exponentUnary', coverageUnary',
    actionUnary', transportUnary', _consumerUnary', _hsameUnary', _provenanceUnary',
    _localCertUnary', _coverageRoute', transportRoute', _consumerRoute',
    _sameConsumerProvenance', _sameHsameProvenance', _provenancePkg',
    _localCertPkg'⟩ := carrier'
  cases sameCoverage
  cases sameAction
  have sameTransport : hsame transportRow transportRow' :=
    transportRoute.trans transportRoute'.symm
  exact
    ⟨sameTransport, transportUnary, transportUnary', transportRoute, transportRoute'⟩

theorem SylowCarrier_prime_power_coverage [AskSetup] [PackageSetup]
    {groupRow subgroupRow primeRow exponentRow coverageRow actionRow transportRow consumerRow
      hsameRow provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SylowCarrier groupRow subgroupRow primeRow exponentRow coverageRow actionRow transportRow
        consumerRow hsameRow provenance localCert bundle pkg →
      UnaryHistory primeRow ∧ UnaryHistory exponentRow ∧ UnaryHistory coverageRow ∧
        Cont groupRow subgroupRow coverageRow ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier
  obtain ⟨_groupUnary, _subgroupUnary, primeUnary, exponentUnary, coverageUnary,
    _actionUnary, _transportUnary, _consumerUnary, _hsameUnary, _provenanceUnary,
    _localCertUnary, coverageRoute, _transportRoute, _consumerRoute,
    _sameConsumerProvenance, _sameHsameProvenance, provenancePkg, _localCertPkg⟩ := carrier
  exact ⟨primeUnary, exponentUnary, coverageUnary, coverageRoute, provenancePkg⟩

theorem SylowCarrier_obligation_closure_surface [AskSetup] [PackageSetup]
    {groupRow subgroupRow primeRow exponentRow coverageRow actionRow transportRow consumerRow
      hsameRow provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SylowCarrier groupRow subgroupRow primeRow exponentRow coverageRow actionRow transportRow
        consumerRow hsameRow provenance localCert bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row provenance ∧
              SylowCarrier groupRow subgroupRow primeRow exponentRow coverageRow actionRow
                transportRow consumerRow hsameRow provenance localCert bundle pkg)
          (fun row : BHist =>
            hsame row groupRow ∨ hsame row subgroupRow ∨ hsame row primeRow ∨
              hsame row exponentRow ∨ hsame row coverageRow ∨ hsame row actionRow ∨
                hsame row transportRow ∨ hsame row consumerRow ∨ hsame row hsameRow ∨
                  hsame row provenance ∨ hsame row localCert)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localCert pkg)
          hsame ∧
        UnaryHistory groupRow ∧ UnaryHistory subgroupRow ∧ UnaryHistory primeRow ∧
          UnaryHistory exponentRow ∧ UnaryHistory coverageRow ∧ UnaryHistory actionRow ∧
            UnaryHistory transportRow ∧ UnaryHistory consumerRow ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localCert pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier
  have carrierPacket :
      SylowCarrier groupRow subgroupRow primeRow exponentRow coverageRow actionRow
        transportRow consumerRow hsameRow provenance localCert bundle pkg :=
    carrier
  have coverageSurface :=
    BEDC.Derived.SylowUp.SylowCarrier_prime_power_coverage
      (groupRow := groupRow) (subgroupRow := subgroupRow) (primeRow := primeRow)
      (exponentRow := exponentRow) (coverageRow := coverageRow) (actionRow := actionRow)
      (transportRow := transportRow) (consumerRow := consumerRow) (hsameRow := hsameRow)
      (provenance := provenance) (localCert := localCert) (bundle := bundle) (pkg := pkg)
      carrier
  obtain ⟨primeUnary, exponentUnary, coverageUnary, _coverageRouteFromPrimePower,
    provenancePkg⟩ := coverageSurface
  obtain ⟨groupUnary, subgroupUnary, _primeUnary, _exponentUnary, _coverageUnary, actionUnary,
    transportUnary, consumerUnary, _hsameUnary, provenanceUnary, localCertUnary,
    _coverageRoute, _transportRoute, _consumerRoute, sameConsumerProvenance,
    _sameHsameProvenance, _provenancePkg, localCertPkg⟩ := carrier
  have provenancePattern :
      hsame provenance groupRow ∨ hsame provenance subgroupRow ∨ hsame provenance primeRow ∨
        hsame provenance exponentRow ∨ hsame provenance coverageRow ∨
          hsame provenance actionRow ∨ hsame provenance transportRow ∨
            hsame provenance consumerRow ∨ hsame provenance hsameRow ∨
              hsame provenance provenance ∨ hsame provenance localCert := by
    right; right; right; right; right; right; right; right; right; left
    exact hsame_refl provenance
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row provenance ∧
              SylowCarrier groupRow subgroupRow primeRow exponentRow coverageRow actionRow
                transportRow consumerRow hsameRow provenance localCert bundle pkg)
          (fun row : BHist =>
            hsame row groupRow ∨ hsame row subgroupRow ∨ hsame row primeRow ∨
              hsame row exponentRow ∨ hsame row coverageRow ∨ hsame row actionRow ∨
                hsame row transportRow ∨ hsame row consumerRow ∨ hsame row hsameRow ∨
                  hsame row provenance ∨ hsame row localCert)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localCert pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro provenance ⟨hsame_refl provenance, carrierPacket⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows sourceRow
        exact ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow.left
      exact provenancePattern
    ledger_sound := by
      intro _row sourceRow
      cases sourceRow.left
      exact ⟨provenanceUnary, provenancePkg, localCertPkg⟩
  }
  exact
    ⟨cert, groupUnary, subgroupUnary, primeUnary, exponentUnary, coverageUnary, actionUnary,
      transportUnary, consumerUnary, provenancePkg, localCertPkg⟩

theorem SylowCarrier_scope_dependency_lock [AskSetup] [PackageSetup]
    {groupRow subgroupRow primeRow exponentRow coverageRow actionRow transportRow consumerRow
      hsameRow provenance localCert publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SylowCarrier groupRow subgroupRow primeRow exponentRow coverageRow actionRow transportRow
        consumerRow hsameRow provenance localCert bundle pkg →
      Cont consumerRow hsameRow publicRead →
        PkgSig bundle publicRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row groupRow ∨ hsame row subgroupRow ∨ hsame row primeRow ∨
                  hsame row exponentRow ∨ hsame row coverageRow ∨ hsame row actionRow ∨
                    hsame row transportRow ∨ hsame row consumerRow ∨ hsame row hsameRow ∨
                      hsame row publicRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont groupRow subgroupRow coverageRow ∧
                  Cont coverageRow actionRow transportRow ∧
                    Cont transportRow consumerRow hsameRow ∧
                      Cont consumerRow hsameRow publicRead ∧ PkgSig bundle publicRead pkg)
              hsame ∧
            UnaryHistory publicRead ∧ Cont groupRow subgroupRow coverageRow ∧
              Cont coverageRow actionRow transportRow := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier publicRoute publicPkg
  obtain ⟨_groupUnary, _subgroupUnary, _primeUnary, _exponentUnary, coverageUnary,
    actionUnary, _transportUnary, consumerUnary, hsameUnary, _provenanceUnary,
    _localCertUnary, coverageRoute, transportRoute, consumerRoute,
    _sameConsumerProvenance, _sameHsameProvenance, _provenancePkg,
    _localCertPkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed consumerUnary hsameUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row groupRow ∨ hsame row subgroupRow ∨ hsame row primeRow ∨
              hsame row exponentRow ∨ hsame row coverageRow ∨ hsame row actionRow ∨
                hsame row transportRow ∨ hsame row consumerRow ∨ hsame row hsameRow ∨
                  hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont groupRow subgroupRow coverageRow ∧
              Cont coverageRow actionRow transportRow ∧
                Cont transportRow consumerRow hsameRow ∧
                  Cont consumerRow hsameRow publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coverageRoute, transportRoute, consumerRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, publicUnary, coverageRoute, transportRoute⟩

theorem SylowCarrier_conjugacy_transport_public_scope [AskSetup] [PackageSetup]
    {groupRow subgroupRow subgroupRow' primeRow exponentRow coverageRow coverageRow' actionRow
      actionRow' transportRow transportRow' consumerRow consumerRow' hsameRow hsameRow'
      provenance provenance' localCert localCert' publicRead publicRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SylowCarrier groupRow subgroupRow primeRow exponentRow coverageRow actionRow transportRow
        consumerRow hsameRow provenance localCert bundle pkg →
      SylowCarrier groupRow subgroupRow' primeRow exponentRow coverageRow' actionRow'
          transportRow' consumerRow' hsameRow' provenance' localCert' bundle pkg →
        hsame coverageRow coverageRow' →
          hsame actionRow actionRow' →
            Cont consumerRow hsameRow publicRead →
              PkgSig bundle publicRead pkg →
                Cont consumerRow' hsameRow' publicRead' →
                  PkgSig bundle publicRead' pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row groupRow ∨ hsame row subgroupRow ∨
                            hsame row primeRow ∨ hsame row exponentRow ∨
                              hsame row coverageRow ∨ hsame row actionRow ∨
                                hsame row transportRow ∨ hsame row consumerRow ∨
                                  hsame row hsameRow ∨ hsame row publicRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont groupRow subgroupRow coverageRow ∧
                            Cont coverageRow actionRow transportRow ∧
                              Cont transportRow consumerRow hsameRow ∧
                                Cont consumerRow hsameRow publicRead ∧
                                  PkgSig bundle publicRead pkg)
                        hsame ∧
                      SemanticNameCert
                          (fun row : BHist => hsame row publicRead' ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row groupRow ∨ hsame row subgroupRow' ∨
                              hsame row primeRow ∨ hsame row exponentRow ∨
                                hsame row coverageRow' ∨ hsame row actionRow' ∨
                                  hsame row transportRow' ∨ hsame row consumerRow' ∨
                                    hsame row hsameRow' ∨ hsame row publicRead')
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont groupRow subgroupRow' coverageRow' ∧
                              Cont coverageRow' actionRow' transportRow' ∧
                                Cont transportRow' consumerRow' hsameRow' ∧
                                  Cont consumerRow' hsameRow' publicRead' ∧
                                    PkgSig bundle publicRead' pkg)
                          hsame ∧
                        hsame transportRow transportRow' ∧
                          Cont coverageRow actionRow transportRow ∧
                            Cont coverageRow' actionRow' transportRow' := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig SemanticNameCert
  intro carrier carrier' sameCoverage sameAction publicRoute publicPkg publicRoute' publicPkg'
  have transportSurface :=
    BEDC.Derived.SylowUp.SylowCarrier_conjugacy_transport
      (groupRow := groupRow) (subgroupRow := subgroupRow) (subgroupRow' := subgroupRow')
      (primeRow := primeRow) (exponentRow := exponentRow) (coverageRow := coverageRow)
      (coverageRow' := coverageRow') (actionRow := actionRow) (actionRow' := actionRow')
      (transportRow := transportRow) (transportRow' := transportRow')
      (consumerRow := consumerRow) (consumerRow' := consumerRow') (hsameRow := hsameRow)
      (hsameRow' := hsameRow') (provenance := provenance) (provenance' := provenance')
      (localCert := localCert) (localCert' := localCert') (bundle := bundle) (pkg := pkg)
      carrier carrier' sameCoverage sameAction
  have publicSurface :=
    BEDC.Derived.SylowUp.SylowCarrier_scope_dependency_lock
      (groupRow := groupRow) (subgroupRow := subgroupRow) (primeRow := primeRow)
      (exponentRow := exponentRow) (coverageRow := coverageRow) (actionRow := actionRow)
      (transportRow := transportRow) (consumerRow := consumerRow) (hsameRow := hsameRow)
      (provenance := provenance) (localCert := localCert) (publicRead := publicRead)
      (bundle := bundle) (pkg := pkg) carrier publicRoute publicPkg
  have publicSurface' :=
    BEDC.Derived.SylowUp.SylowCarrier_scope_dependency_lock
      (groupRow := groupRow) (subgroupRow := subgroupRow') (primeRow := primeRow)
      (exponentRow := exponentRow) (coverageRow := coverageRow') (actionRow := actionRow')
      (transportRow := transportRow') (consumerRow := consumerRow') (hsameRow := hsameRow')
      (provenance := provenance') (localCert := localCert') (publicRead := publicRead')
      (bundle := bundle) (pkg := pkg) carrier' publicRoute' publicPkg'
  obtain ⟨sameTransport, _transportUnary, _transportUnary', transportRoute,
    transportRoute'⟩ := transportSurface
  obtain ⟨publicCert, _publicUnary, _coverageRoute, _transportRoute⟩ := publicSurface
  obtain ⟨publicCert', _publicUnary', _coverageRoute', _transportRoute'⟩ := publicSurface'
  exact ⟨publicCert, publicCert', sameTransport, transportRoute, transportRoute'⟩

theorem SylowCarrier_public_readback_consumes_namecert_obligations [AskSetup] [PackageSetup]
    {groupRow subgroupRow primeRow exponentRow coverageRow actionRow transportRow consumerRow
      hsameRow provenance localCert publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SylowCarrier groupRow subgroupRow primeRow exponentRow coverageRow actionRow transportRow
        consumerRow hsameRow provenance localCert bundle pkg →
      Cont consumerRow hsameRow publicRead →
        PkgSig bundle publicRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row provenance ∧
                  SylowCarrier groupRow subgroupRow primeRow exponentRow coverageRow actionRow
                    transportRow consumerRow hsameRow provenance localCert bundle pkg)
              (fun row : BHist =>
                hsame row groupRow ∨ hsame row subgroupRow ∨ hsame row primeRow ∨
                  hsame row exponentRow ∨ hsame row coverageRow ∨ hsame row actionRow ∨
                    hsame row transportRow ∨ hsame row consumerRow)
              (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
              hsame ∧
            SemanticNameCert
                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row groupRow ∨ hsame row subgroupRow ∨ hsame row primeRow ∨
                    hsame row exponentRow ∨ hsame row coverageRow ∨ hsame row actionRow ∨
                      hsame row transportRow ∨ hsame row consumerRow ∨ hsame row hsameRow ∨
                        hsame row publicRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont groupRow subgroupRow coverageRow ∧
                    Cont coverageRow actionRow transportRow ∧
                      Cont transportRow consumerRow hsameRow ∧
                        Cont consumerRow hsameRow publicRead ∧ PkgSig bundle publicRead pkg)
                hsame ∧
              Cont groupRow subgroupRow coverageRow ∧ Cont coverageRow actionRow transportRow ∧
                Cont transportRow consumerRow hsameRow ∧ Cont consumerRow hsameRow publicRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig SemanticNameCert
  intro carrier publicRoute publicPkg
  have namecertSurface :=
    BEDC.Derived.SylowUp.SylowCarrier_namecert_obligations
      (groupRow := groupRow) (subgroupRow := subgroupRow) (primeRow := primeRow)
      (exponentRow := exponentRow) (coverageRow := coverageRow) (actionRow := actionRow)
      (transportRow := transportRow) (consumerRow := consumerRow) (hsameRow := hsameRow)
      (provenance := provenance) (localCert := localCert) (bundle := bundle) (pkg := pkg)
      carrier
  have publicSurface :=
    BEDC.Derived.SylowUp.SylowCarrier_scope_dependency_lock
      (groupRow := groupRow) (subgroupRow := subgroupRow) (primeRow := primeRow)
      (exponentRow := exponentRow) (coverageRow := coverageRow) (actionRow := actionRow)
      (transportRow := transportRow) (consumerRow := consumerRow) (hsameRow := hsameRow)
      (provenance := provenance) (localCert := localCert) (publicRead := publicRead)
      (bundle := bundle) (pkg := pkg) carrier publicRoute publicPkg
  obtain ⟨namecert, _groupUnary, _subgroupUnary, _primeUnary, _exponentUnary,
    _coverageUnary, _actionUnary, _transportUnary, _consumerUnary, provenancePkg⟩ :=
    namecertSurface
  obtain ⟨publicCert, _publicUnary, coverageRoute, transportRoute⟩ := publicSurface
  obtain ⟨_groupUnary', _subgroupUnary', _primeUnary', _exponentUnary', _coverageUnary',
    _actionUnary', _transportUnary', _consumerUnary', _hsameUnary', _provenanceUnary',
    _localCertUnary, _coverageRoute, _transportRoute, consumerRoute,
    _sameConsumerProvenance, _sameHsameProvenance, _provenancePkg, _localCertPkg⟩ :=
    carrier
  exact
    ⟨namecert, publicCert, coverageRoute, transportRoute, consumerRoute, publicRoute,
      provenancePkg, publicPkg⟩

end BEDC.Derived.SylowUp
