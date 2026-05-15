import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ZetaContinuationWitnessPacket [AskSetup] [PackageSetup]
    (basic eta analytic pole functional zeroLedger gamma transports routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Cont basic eta analytic ∧
    Cont analytic functional transports ∧
    Cont pole zeroLedger gamma ∧
    Cont transports routes provenance ∧
    PkgSig bundle name pkg ∧
    PkgSig bundle provenance pkg

theorem ZetaContinuationWitnessPacket_dependency_ledger [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports routes
      provenance name bundle pkg →
      Cont basic eta' analytic' →
      Cont analytic' functional transports' →
      Cont transports' routes provenance' →
      PkgSig bundle provenance' pkg →
      hsame eta eta' →
      hsame analytic analytic' /\ hsame transports transports' /\
        hsame provenance provenance' /\ PkgSig bundle name pkg /\
          PkgSig bundle provenance' pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg
  intro packet basicRoute functionalRoute provenanceRoute provenancePkg etaSame
  cases packet with
  | intro basicAnalytic rest =>
      cases rest with
      | intro analyticTransport rest =>
          cases rest with
          | intro _functionalGamma rest =>
              cases rest with
              | intro transportProvenance rest =>
                  cases rest with
                  | intro namePkg _provenancePkg =>
                      have analyticSame : hsame analytic analytic' :=
                        cont_respects_hsame (hsame_refl basic) etaSame basicAnalytic basicRoute
                      have transportsSame : hsame transports transports' :=
                        cont_respects_hsame analyticSame (hsame_refl functional) analyticTransport
                          functionalRoute
                      have provenanceSame : hsame provenance provenance' :=
                        cont_respects_hsame transportsSame (hsame_refl routes) transportProvenance
                          provenanceRoute
                      exact
                        ⟨analyticSame, transportsSame, provenanceSame, namePkg,
                          provenancePkg⟩

theorem ZetaContinuationWitnessPacket_public_export [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      exportRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
        transports routes provenance name bundle pkg →
      UnaryHistory routes →
        UnaryHistory name →
          Cont routes name exportRow →
            UnaryHistory exportRow ∧ hsame exportRow (append routes name) ∧
              PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet routesUnary nameUnary routesNameExport
  obtain ⟨_basicEtaAnalytic, _analyticFunctionalTransports, _poleZeroLedgerGamma,
    _transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have exportUnary : UnaryHistory exportRow :=
    unary_cont_closed routesUnary nameUnary routesNameExport
  exact ⟨exportUnary, routesNameExport, namePkg, provenancePkg⟩

theorem ZetaContinuationWitnessPacket_public_source_lock_handoff [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' provenance' exportRow exportRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
        transports routes provenance name bundle pkg →
      Cont basic eta' analytic' →
        Cont analytic' functional transports' →
          Cont transports' routes provenance' →
            Cont routes name exportRow →
              Cont routes name exportRow' →
                PkgSig bundle provenance' pkg →
                  hsame eta eta' →
                    hsame analytic analytic' ∧ hsame transports transports' ∧
                      hsame provenance provenance' ∧ hsame exportRow exportRow' ∧
                        PkgSig bundle name pkg ∧ PkgSig bundle provenance' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro packet basicRoute functionalRoute provenanceRoute exportRoute exportRoute'
    provenancePkg etaSame
  have ledger :=
    ZetaContinuationWitnessPacket_dependency_ledger
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := eta') (analytic' := analytic')
      (transports' := transports') (provenance' := provenance') (bundle := bundle)
      (pkg := pkg) packet basicRoute functionalRoute provenanceRoute provenancePkg etaSame
  obtain ⟨analyticSame, transportsSame, provenanceSame, namePkg, provenancePkg'⟩ := ledger
  have exportSame : hsame exportRow exportRow' :=
    cont_respects_hsame (hsame_refl routes) (hsame_refl name) exportRoute exportRoute'
  exact
    ⟨analyticSame, transportsSame, provenanceSame, exportSame, namePkg, provenancePkg'⟩

theorem ZetaContinuationWitnessPacket_source_boundary [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
      routes provenance name bundle pkg →
      Cont basic eta' analytic' →
      Cont analytic' functional transports' →
      hsame eta eta' →
      hsame analytic analytic' ∧ hsame transports transports' ∧ PkgSig bundle name pkg ∧
        PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro packet basicRoute functionalRoute etaSame
  obtain ⟨basicAnalytic, analyticTransport, _poleGamma, _transportProvenance, namePkg,
    provenancePkg⟩ := packet
  have analyticSame : hsame analytic analytic' :=
    cont_respects_hsame (hsame_refl basic) etaSame basicAnalytic basicRoute
  have transportsSame : hsame transports transports' :=
    cont_respects_hsame analyticSame (hsame_refl functional) analyticTransport functionalRoute
  exact ⟨analyticSame, transportsSame, namePkg, provenancePkg⟩

theorem ZetaContinuationWitnessPacket_gamma_boundary [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      zeroLedger' gamma' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
      routes provenance name bundle pkg →
      Cont pole zeroLedger' gamma' →
      hsame zeroLedger zeroLedger' →
      hsame gamma gamma' ∧ PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro packet gammaRoute zeroLedgerSame
  obtain ⟨_basicAnalytic, _analyticTransport, poleGamma, _transportProvenance, namePkg,
    provenancePkg⟩ := packet
  have gammaSame : hsame gamma gamma' :=
    cont_respects_hsame (hsame_refl pole) zeroLedgerSame poleGamma gammaRoute
  exact ⟨gammaSame, namePkg, provenancePkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
