import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MonotoneCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MonotoneCauchyCarrier [AskSetup] [PackageSetup]
    (regular schedule modulus ledger interval realSeal transportRow route provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory regular ∧ UnaryHistory schedule ∧ UnaryHistory modulus ∧
    UnaryHistory ledger ∧ UnaryHistory interval ∧ UnaryHistory realSeal ∧
      UnaryHistory transportRow ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory nameRow ∧ Cont regular schedule modulus ∧
          Cont modulus ledger interval ∧ Cont interval realSeal nameRow ∧
            Cont transportRow route provenance ∧ PkgSig bundle nameRow pkg

theorem MonotoneCauchyCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {regular schedule modulus ledger interval realSeal transportRow route provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
        provenance nameRow bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
            provenance nameRow bundle pkg ∧ hsame row nameRow)
        (fun _row : BHist =>
          MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
            provenance nameRow bundle pkg ∧ Cont regular schedule modulus ∧
              Cont modulus ledger interval ∧ Cont interval realSeal nameRow ∧
                Cont transportRow route provenance)
        (fun row : BHist => PkgSig bundle nameRow pkg ∧ hsame row nameRow)
        hsame := by
  intro carrier
  have carrierPacket := carrier
  obtain ⟨_regularUnary, _scheduleUnary, _modulusUnary, _ledgerUnary, _intervalUnary,
    _realSealUnary, _transportRowUnary, _routeUnary, _provenanceUnary, _nameRowUnary,
    regularScheduleModulus, modulusLedgerInterval, intervalRealSealNameRow,
    transportRouteProvenance, nameRowPkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro nameRow (And.intro carrierPacket (hsame_refl nameRow))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨source.left, regularScheduleModulus, modulusLedgerInterval, intervalRealSealNameRow,
          transportRouteProvenance⟩
    ledger_sound := by
      intro _row source
      exact ⟨nameRowPkg, source.right⟩
  }

theorem MonotoneCauchyCarrier_located_interval_handoff [AskSetup] [PackageSetup]
    {regular schedule modulus ledger interval realSeal transportRow route provenance
      nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
        provenance nameRow bundle pkg ->
      UnaryHistory interval ∧ UnaryHistory realSeal ∧ hsame interval (append modulus ledger) ∧
        hsame nameRow (append (append modulus ledger) realSeal) ∧ PkgSig bundle nameRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier
  obtain ⟨_regularUnary, _scheduleUnary, _modulusUnary, _ledgerUnary, intervalUnary,
    realSealUnary, _transportRowUnary, _routeUnary, _provenanceUnary, _nameRowUnary,
    _regularScheduleModulus, modulusLedgerInterval, intervalRealSealNameRow,
    _transportRouteProvenance, nameRowPkg⟩ := carrier
  exact
    ⟨intervalUnary, realSealUnary, modulusLedgerInterval, by
      cases intervalRealSealNameRow
      cases modulusLedgerInterval
      rfl, nameRowPkg⟩

theorem MonotoneCauchyCarrier_real_seal_boundary [AskSetup] [PackageSetup]
    {regular schedule modulus ledger interval realSeal transportRow route provenance
      nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
        provenance nameRow bundle pkg ->
      UnaryHistory regular ∧ UnaryHistory schedule ∧ UnaryHistory modulus ∧
        UnaryHistory ledger ∧ UnaryHistory interval ∧ UnaryHistory realSeal ∧
          Cont regular schedule modulus ∧ Cont modulus ledger interval ∧
            Cont interval realSeal nameRow ∧ PkgSig bundle nameRow pkg := by
  intro carrier
  obtain ⟨regularUnary, scheduleUnary, modulusUnary, ledgerUnary, intervalUnary,
    realSealUnary, _transportRowUnary, _routeUnary, _provenanceUnary, _nameRowUnary,
    regularScheduleModulus, modulusLedgerInterval, intervalRealSealNameRow,
    _transportRouteProvenance, nameRowPkg⟩ := carrier
  exact
    ⟨regularUnary, scheduleUnary, modulusUnary, ledgerUnary, intervalUnary, realSealUnary,
      regularScheduleModulus, modulusLedgerInterval, intervalRealSealNameRow, nameRowPkg⟩

theorem MonotoneCauchyCarrier_common_window_classifier [AskSetup] [PackageSetup]
    {regular schedule modulus ledger interval realSeal transportRow route provenance nameRow
      commonWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
        provenance nameRow bundle pkg ->
      Cont schedule modulus commonWindow ->
        PkgSig bundle commonWindow pkg ->
          UnaryHistory regular ∧ UnaryHistory schedule ∧ UnaryHistory modulus ∧
            UnaryHistory ledger ∧ UnaryHistory commonWindow ∧
              Cont regular schedule modulus ∧ Cont schedule modulus commonWindow ∧
                Cont modulus ledger interval ∧ Cont interval realSeal nameRow ∧
                  PkgSig bundle nameRow pkg ∧ PkgSig bundle commonWindow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier scheduleModulusCommonWindow commonWindowPkg
  obtain ⟨regularUnary, scheduleUnary, modulusUnary, ledgerUnary, _intervalUnary,
    _realSealUnary, _transportRowUnary, _routeUnary, _provenanceUnary, _nameRowUnary,
    regularScheduleModulus, modulusLedgerInterval, intervalRealSealNameRow,
    _transportRouteProvenance, nameRowPkg⟩ := carrier
  have commonWindowUnary : UnaryHistory commonWindow :=
    unary_cont_closed scheduleUnary modulusUnary scheduleModulusCommonWindow
  exact
    ⟨regularUnary, scheduleUnary, modulusUnary, ledgerUnary, commonWindowUnary,
      regularScheduleModulus, scheduleModulusCommonWindow, modulusLedgerInterval,
      intervalRealSealNameRow, nameRowPkg, commonWindowPkg⟩

theorem MonotoneCauchyCarrier_tail_window_scope_lock [AskSetup] [PackageSetup]
    {regular schedule modulus ledger interval realSeal transportRow route provenance nameRow
      commonWindow schedule' modulus' commonWindow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
        provenance nameRow bundle pkg ->
      Cont schedule modulus commonWindow ->
        Cont schedule' modulus' commonWindow' ->
          hsame schedule schedule' ->
            hsame modulus modulus' ->
              UnaryHistory commonWindow ∧ UnaryHistory commonWindow' ∧
                hsame commonWindow commonWindow' ∧ Cont transportRow route provenance ∧
                  PkgSig bundle nameRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier scheduleModulusCommonWindow scheduleModulusCommonWindow'
    sameSchedule sameModulus
  obtain ⟨_regularUnary, scheduleUnary, modulusUnary, _ledgerUnary, _intervalUnary,
    _realSealUnary, _transportRowUnary, _routeUnary, _provenanceUnary, _nameRowUnary,
    _regularScheduleModulus, _modulusLedgerInterval, _intervalRealSealNameRow,
    transportRouteProvenance, nameRowPkg⟩ := carrier
  have commonWindowUnary : UnaryHistory commonWindow :=
    unary_cont_closed scheduleUnary modulusUnary scheduleModulusCommonWindow
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have commonWindowUnary' : UnaryHistory commonWindow' :=
    unary_cont_closed scheduleUnary' modulusUnary' scheduleModulusCommonWindow'
  have sameCommonWindow : hsame commonWindow commonWindow' :=
    cont_respects_hsame sameSchedule sameModulus scheduleModulusCommonWindow
      scheduleModulusCommonWindow'
  exact
    ⟨commonWindowUnary, commonWindowUnary', sameCommonWindow, transportRouteProvenance,
      nameRowPkg⟩

theorem MonotoneCauchyCarrier_modulus_tail_stability [AskSetup] [PackageSetup]
    {regular schedule modulus ledger interval realSeal transportRow route provenance nameRow
      regular' schedule' modulus' ledger' interval' realSeal' nameRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
        provenance nameRow bundle pkg ->
      hsame regular regular' -> hsame schedule schedule' -> hsame modulus modulus' ->
        hsame ledger ledger' -> hsame realSeal realSeal' ->
          Cont regular' schedule' modulus' -> Cont modulus' ledger' interval' ->
            Cont interval' realSeal' nameRow' -> PkgSig bundle nameRow' pkg ->
              MonotoneCauchyCarrier regular' schedule' modulus' ledger' interval' realSeal'
                  transportRow route provenance nameRow' bundle pkg ∧
                hsame interval interval' ∧ hsame realSeal realSeal' ∧
                  hsame nameRow nameRow' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier sameRegular sameSchedule sameModulus sameLedger sameRealSeal
    regularScheduleModulus' modulusLedgerInterval' intervalRealSealNameRow' nameRowPkg'
  obtain ⟨regularUnary, scheduleUnary, modulusUnary, ledgerUnary, intervalUnary,
    realSealUnary, transportRowUnary, routeUnary, provenanceUnary, nameRowUnary,
    regularScheduleModulus, modulusLedgerInterval, intervalRealSealNameRow,
    transportRouteProvenance, _nameRowPkg⟩ := carrier
  have sameInterval : hsame interval interval' :=
    cont_respects_hsame sameModulus sameLedger modulusLedgerInterval modulusLedgerInterval'
  have sameNameRow : hsame nameRow nameRow' :=
    cont_respects_hsame sameInterval sameRealSeal intervalRealSealNameRow
      intervalRealSealNameRow'
  have transported :
      MonotoneCauchyCarrier regular' schedule' modulus' ledger' interval' realSeal'
          transportRow route provenance nameRow' bundle pkg :=
    ⟨unary_transport regularUnary sameRegular,
      unary_transport scheduleUnary sameSchedule,
      unary_transport modulusUnary sameModulus,
      unary_transport ledgerUnary sameLedger,
      unary_transport intervalUnary sameInterval,
      unary_transport realSealUnary sameRealSeal,
      transportRowUnary,
      routeUnary,
      provenanceUnary,
      unary_transport nameRowUnary sameNameRow,
      regularScheduleModulus',
      modulusLedgerInterval',
      intervalRealSealNameRow',
      transportRouteProvenance,
      nameRowPkg'⟩
  exact ⟨transported, sameInterval, sameRealSeal, sameNameRow⟩

theorem MonotoneCauchyCarrier_public_seal_window_determinacy
    [AskSetup] [PackageSetup]
    {regular schedule modulus ledger interval realSeal transportRow route provenance nameRow
      regular' schedule' modulus' ledger' interval' realSeal' nameRow' commonWindow
      commonWindow' sealRead sealRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
        provenance nameRow bundle pkg ->
      MonotoneCauchyCarrier regular' schedule' modulus' ledger' interval' realSeal'
          transportRow route provenance nameRow' bundle pkg ->
        Cont schedule modulus commonWindow ->
          Cont schedule' modulus' commonWindow' ->
            hsame schedule schedule' ->
              hsame modulus modulus' ->
                hsame ledger ledger' ->
                  hsame realSeal realSeal' ->
                    Cont interval realSeal sealRead ->
                      Cont interval' realSeal' sealRead' ->
                        hsame sealRead sealRead' ∧ hsame commonWindow commonWindow' ∧
                          PkgSig bundle nameRow pkg ∧ PkgSig bundle nameRow' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier carrier' scheduleModulusWindow scheduleModulusWindow' sameSchedule
    sameModulus sameLedger sameRealSeal intervalRealSealRead intervalRealSealRead'
  obtain ⟨_regularUnary, _scheduleUnary, _modulusUnary, _ledgerUnary, _intervalUnary,
    _realSealUnary, _transportRowUnary, _routeUnary, _provenanceUnary, _nameRowUnary,
    _regularScheduleModulus, modulusLedgerInterval, _intervalRealSealNameRow,
    _transportRouteProvenance, nameRowPkg⟩ := carrier
  obtain ⟨_regularUnary', _scheduleUnary', _modulusUnary', _ledgerUnary', _intervalUnary',
    _realSealUnary', _transportRowUnary', _routeUnary', _provenanceUnary', _nameRowUnary',
    _regularScheduleModulus', modulusLedgerInterval', _intervalRealSealNameRow',
    _transportRouteProvenance', nameRowPkg'⟩ := carrier'
  have sameCommonWindow : hsame commonWindow commonWindow' :=
    cont_respects_hsame sameSchedule sameModulus scheduleModulusWindow
      scheduleModulusWindow'
  have sameInterval : hsame interval interval' :=
    cont_respects_hsame sameModulus sameLedger modulusLedgerInterval modulusLedgerInterval'
  have sameSealRead : hsame sealRead sealRead' :=
    cont_respects_hsame sameInterval sameRealSeal intervalRealSealRead
      intervalRealSealRead'
  exact ⟨sameSealRead, sameCommonWindow, nameRowPkg, nameRowPkg'⟩

theorem MonotoneCauchyCarrier_real_seal_factorization_obligation [AskSetup] [PackageSetup]
    {regular schedule modulus ledger interval realSeal transportRow route provenance nameRow
      commonWindow sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
        provenance nameRow bundle pkg ->
      Cont schedule modulus commonWindow ->
        Cont interval realSeal sealRead ->
          UnaryHistory commonWindow ∧ UnaryHistory sealRead ∧
            hsame nameRow (append interval realSeal) ∧
              hsame nameRow (append (append modulus ledger) realSeal) ∧
                Cont transportRow route provenance ∧ PkgSig bundle nameRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier scheduleModulusCommonWindow intervalRealSealRead
  obtain ⟨_regularUnary, scheduleUnary, modulusUnary, _ledgerUnary, intervalUnary,
    realSealUnary, _transportRowUnary, _routeUnary, _provenanceUnary, _nameRowUnary,
    _regularScheduleModulus, modulusLedgerInterval, intervalRealSealNameRow,
    transportRouteProvenance, nameRowPkg⟩ := carrier
  have commonWindowUnary : UnaryHistory commonWindow :=
    unary_cont_closed scheduleUnary modulusUnary scheduleModulusCommonWindow
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed intervalUnary realSealUnary intervalRealSealRead
  have sameNameIntervalSeal : hsame nameRow (append interval realSeal) := by
    exact intervalRealSealNameRow
  have sameNameLedgerSeal : hsame nameRow (append (append modulus ledger) realSeal) := by
    cases intervalRealSealNameRow
    cases modulusLedgerInterval
    rfl
  exact
    ⟨commonWindowUnary, sealReadUnary, sameNameIntervalSeal, sameNameLedgerSeal,
      transportRouteProvenance, nameRowPkg⟩

end BEDC.Derived.MonotoneCauchyUp
