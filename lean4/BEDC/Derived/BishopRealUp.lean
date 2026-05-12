import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BishopRealPacket [AskSetup] [PackageSetup]
    (schedule regular dyadic modulus located apartness realSeal transport routes provenance
      nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory schedule ∧ UnaryHistory regular ∧ UnaryHistory dyadic ∧
    UnaryHistory modulus ∧ UnaryHistory located ∧ UnaryHistory apartness ∧
      UnaryHistory realSeal ∧ UnaryHistory transport ∧ UnaryHistory routes ∧
        UnaryHistory provenance ∧ UnaryHistory nameCert ∧ Cont schedule regular dyadic ∧
          Cont dyadic modulus realSeal ∧ Cont transport routes provenance ∧
            PkgSig bundle provenance pkg

theorem BishopRealPacket_located_apartness_transport [AskSetup] [PackageSetup]
    {schedule regular dyadic modulus located apartness realSeal transport routes provenance
      nameCert schedule' regular' dyadic' modulus' located' apartness' realSeal'
      transport' routes' provenance' nameCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRealPacket schedule regular dyadic modulus located apartness realSeal transport routes
        provenance nameCert bundle pkg ->
      hsame schedule schedule' ->
        hsame regular regular' ->
          hsame dyadic dyadic' ->
            hsame modulus modulus' ->
              hsame located located' ->
                hsame apartness apartness' ->
                  hsame realSeal realSeal' ->
                    hsame transport transport' ->
                      hsame routes routes' ->
                        hsame provenance provenance' ->
                          hsame nameCert nameCert' ->
                            Cont schedule' regular' dyadic' ->
                              Cont dyadic' modulus' realSeal' ->
                                Cont transport' routes' provenance' ->
                                  PkgSig bundle provenance' pkg ->
                                    BishopRealPacket schedule' regular' dyadic' modulus'
                                        located' apartness' realSeal' transport' routes'
                                        provenance' nameCert' bundle pkg ∧
                                      hsame realSeal realSeal' ∧ hsame located located' ∧
                                        hsame apartness apartness' := by
  intro packet sameSchedule sameRegular sameDyadic sameModulus sameLocated
  intro sameApartness sameSeal sameTransport sameRoutes sameProvenance sameNameCert
  intro scheduleRegularDyadic dyadicModulusSeal transportRoutesProvenance provenancePkg
  rcases packet with
    ⟨scheduleUnary, regularUnary, dyadicUnary, modulusUnary, locatedUnary,
      apartnessUnary, sealUnary, transportUnary, routesUnary, provenanceUnary, nameCertUnary,
      _scheduleRegularDyadic, _dyadicModulusSeal, _transportRoutesProvenance,
      _provenancePkg⟩
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have regularUnary' : UnaryHistory regular' :=
    unary_transport regularUnary sameRegular
  have dyadicUnary' : UnaryHistory dyadic' :=
    unary_transport dyadicUnary sameDyadic
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have locatedUnary' : UnaryHistory located' :=
    unary_transport locatedUnary sameLocated
  have apartnessUnary' : UnaryHistory apartness' :=
    unary_transport apartnessUnary sameApartness
  have sealUnary' : UnaryHistory realSeal' :=
    unary_transport sealUnary sameSeal
  have transportUnary' : UnaryHistory transport' :=
    unary_transport transportUnary sameTransport
  have routesUnary' : UnaryHistory routes' :=
    unary_transport routesUnary sameRoutes
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have nameCertUnary' : UnaryHistory nameCert' :=
    unary_transport nameCertUnary sameNameCert
  exact
    ⟨⟨scheduleUnary', regularUnary', dyadicUnary', modulusUnary', locatedUnary',
        apartnessUnary', sealUnary', transportUnary', routesUnary', provenanceUnary',
        nameCertUnary', scheduleRegularDyadic, dyadicModulusSeal,
        transportRoutesProvenance, provenancePkg⟩,
      sameSeal, sameLocated, sameApartness⟩

theorem BishopRealPacket_standard_finite_packet_bridge [AskSetup] [PackageSetup]
    {schedule regular endpoint modulus located apart sealRow transport route provenance ledger
      bridge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory schedule ->
      UnaryHistory regular ->
        UnaryHistory endpoint ->
          UnaryHistory modulus ->
            UnaryHistory located ->
              UnaryHistory apart ->
                UnaryHistory sealRow ->
                  UnaryHistory transport ->
                    UnaryHistory route ->
                      UnaryHistory provenance ->
                        UnaryHistory ledger ->
                          Cont schedule regular endpoint ->
                            Cont endpoint modulus sealRow ->
                              Cont located apart bridge ->
                                Cont route sealRow ledger ->
                                  PkgSig bundle provenance pkg ->
                                    PkgSig bundle ledger pkg ->
                                      PkgSig bundle bridge pkg ->
                                        SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row bridge ∧ UnaryHistory row ∧
                                              Cont located apart row ∧ PkgSig bundle row pkg)
                                          (fun row : BHist =>
                                            UnaryHistory schedule ∧ UnaryHistory regular ∧
                                              UnaryHistory endpoint ∧ UnaryHistory modulus ∧
                                                UnaryHistory located ∧ UnaryHistory apart ∧
                                                  UnaryHistory sealRow ∧
                                                    Cont schedule regular endpoint ∧
                                                      Cont endpoint modulus sealRow ∧
                                                        Cont located apart row)
                                          (fun row : BHist =>
                                            PkgSig bundle row pkg ∧ PkgSig bundle ledger pkg ∧
                                              Cont route sealRow ledger)
                                          (fun row row' : BHist =>
                                            psame bundle pkg pkg ∧ hsame row row') := by
  intro scheduleUnary regularUnary endpointUnary modulusUnary locatedUnary apartUnary sealRowUnary
    _transportUnary _routeUnary _provenanceUnary _ledgerUnary scheduleRegularEndpoint
    endpointModulusSeal locatedApartBridge routeSealLedger _provenancePkg ledgerPkg bridgePkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro bridge ⟨hsame_refl bridge, unary_cont_closed locatedUnary apartUnary
          locatedApartBridge, locatedApartBridge, bridgePkg⟩
      equiv_refl := by
        intro row sourceRow
        exact ⟨PkgSig_psame_intro sourceRow.right.right.right sourceRow.right.right.right
          (hsame_refl row), hsame_refl row⟩
      equiv_symm := by
        intro _row _row' classified
        exact ⟨classified.left, hsame_symm classified.right⟩
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact ⟨leftClassified.left, hsame_trans leftClassified.right rightClassified.right⟩
      carrier_respects_equiv := by
        intro _row _row' classified sourceRow
        cases classified.right
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨scheduleUnary, regularUnary, endpointUnary, modulusUnary, locatedUnary, apartUnary,
          sealRowUnary, scheduleRegularEndpoint, endpointModulusSeal, sourceRow.right.right.left⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right.right, ledgerPkg, routeSealLedger⟩
  }

theorem BishopRealPacket_regseqrat_readback [AskSetup] [PackageSetup]
    {schedule regular dyadic modulus located apartness realSeal transport routes provenance
      nameCert readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRealPacket schedule regular dyadic modulus located apartness realSeal transport routes
        provenance nameCert bundle pkg ->
      Cont regular schedule readback ->
        PkgSig bundle readback pkg ->
          UnaryHistory schedule ∧ UnaryHistory regular ∧ UnaryHistory dyadic ∧
            UnaryHistory modulus ∧ UnaryHistory realSeal ∧ UnaryHistory readback ∧
              Cont regular schedule readback ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle readback pkg := by
  intro packet regularScheduleReadback readbackPkg
  rcases packet with
    ⟨scheduleUnary, regularUnary, dyadicUnary, modulusUnary, _locatedUnary,
      _apartnessUnary, realSealUnary, _transportUnary, _routesUnary, _provenanceUnary,
      _nameCertUnary, _scheduleRegularDyadic, _dyadicModulusSeal, _routeProvenance,
      provenancePkg⟩
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed regularUnary scheduleUnary regularScheduleReadback
  exact
    ⟨scheduleUnary, regularUnary, dyadicUnary, modulusUnary, realSealUnary, readbackUnary,
      regularScheduleReadback, provenancePkg, readbackPkg⟩

end BEDC.Derived.BishopRealUp
