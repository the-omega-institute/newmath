import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ComputableRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ComputableRealSourcePacket [AskSetup] [PackageSetup]
    (stream modulus dyadic regseq «seal» transport routes provenance name endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧ UnaryHistory regseq ∧
    UnaryHistory «seal» ∧ Cont stream modulus transport ∧ Cont dyadic regseq routes ∧
      Cont transport routes provenance ∧ Cont provenance name endpoint ∧
        PkgSig bundle endpoint pkg

theorem ComputableRealSourcePacket_ledger_coverage [AskSetup] [PackageSetup]
    {stream modulus dyadic regseq «seal» transport routes provenance name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ComputableRealSourcePacket stream modulus dyadic regseq «seal» transport routes provenance
        name endpoint bundle pkg ->
      UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧ UnaryHistory regseq ∧
        UnaryHistory «seal» ∧ Cont stream modulus transport ∧ Cont dyadic regseq routes ∧
          Cont transport routes provenance ∧ Cont provenance name endpoint ∧
            PkgSig bundle endpoint pkg := by
  intro packet
  constructor
  · exact packet.left
  · constructor
    · exact packet.right.left
    · constructor
      · exact packet.right.right.left
      · constructor
        · exact packet.right.right.right.left
        · constructor
          · exact packet.right.right.right.right.left
          · constructor
            · exact packet.right.right.right.right.right.left
            · constructor
              · exact packet.right.right.right.right.right.right.left
              · constructor
                · exact packet.right.right.right.right.right.right.right.left
                · constructor
                  · exact packet.right.right.right.right.right.right.right.right.left
                  · exact packet.right.right.right.right.right.right.right.right.right

def ComputableRealSource [AskSetup] [PackageSetup]
    (schedule modulus dyadic regular sealRow transport route provenance registration
      approximationWindow sealWindow packet : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
    UnaryHistory regular ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory registration ∧
        Cont schedule modulus approximationWindow ∧ Cont regular sealRow sealWindow ∧
          Cont approximationWindow sealWindow packet ∧ PkgSig bundle packet pkg

theorem ComputableRealSource_namecert_obligation_surface [AskSetup] [PackageSetup]
    {schedule modulus dyadic regular sealRow transport route provenance registration
      approximationWindow sealWindow packet : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ComputableRealSource schedule modulus dyadic regular sealRow transport route provenance
        registration approximationWindow sealWindow packet bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          hsame row packet ∧
            ComputableRealSource schedule modulus dyadic regular sealRow transport route
              provenance registration approximationWindow sealWindow row bundle pkg)
        (fun _row : BHist =>
          UnaryHistory packet ∧ Cont schedule modulus approximationWindow ∧
            Cont regular sealRow sealWindow)
        (fun _row : BHist =>
          PkgSig bundle packet pkg ∧ UnaryHistory provenance ∧ UnaryHistory registration)
        (fun row row' : BHist => PkgSig bundle row pkg ∧ hsame row row') := by
  intro source
  have sourceProof := source
  obtain ⟨scheduleUnary, modulusUnary, dyadicUnary, regularUnary, sealUnary,
    transportUnary, routeUnary, provenanceUnary, registrationUnary, approximationRow,
    sealWindowCont, packetRow, packetSig⟩ := source
  have packetUnary : UnaryHistory packet :=
    unary_cont_closed (unary_cont_closed scheduleUnary modulusUnary approximationRow)
      (unary_cont_closed regularUnary sealUnary sealWindowCont) packetRow
  let SourceSpec : BHist -> Prop :=
    fun row : BHist =>
      hsame row packet ∧
        ComputableRealSource schedule modulus dyadic regular sealRow transport route provenance
          registration approximationWindow sealWindow row bundle pkg
  let PatternSpec : BHist -> Prop :=
    fun _row : BHist =>
      UnaryHistory packet ∧ Cont schedule modulus approximationWindow ∧
        Cont regular sealRow sealWindow
  let LedgerPolicy : BHist -> Prop :=
    fun _row : BHist =>
      PkgSig bundle packet pkg ∧ UnaryHistory provenance ∧ UnaryHistory registration
  let ClassifierSpec : BHist -> BHist -> Prop :=
    fun row row' : BHist => PkgSig bundle row pkg ∧ hsame row row'
  have packetSource : SourceSpec packet :=
    ⟨hsame_refl packet, sourceProof⟩
  have core : NameCert SourceSpec ClassifierSpec := {
    carrier_inhabited := Exists.intro packet packetSource
    equiv_refl := by
      intro row rowSource
      obtain ⟨_scheduleUnary, _modulusUnary, _dyadicUnary, _regularUnary, _sealUnary,
        _transportUnary, _routeUnary, _provenanceUnary, _registrationUnary,
        _approximationRow, _sealWindowCont, _packetRow, rowPkg⟩ := rowSource.right
      exact ⟨rowPkg, hsame_refl row⟩
    equiv_symm := by
      intro row row' classified
      cases classified.right
      exact ⟨classified.left, hsame_refl row⟩
    equiv_trans := by
      intro row row' row'' classifiedLeft classifiedRight
      exact ⟨classifiedLeft.left, hsame_trans classifiedLeft.right classifiedRight.right⟩
    carrier_respects_equiv := by
      intro row row' classified rowSource
      cases classified.right
      exact rowSource
  }
  exact {
    core := core
    pattern_sound := by
      intro _row _rowSource
      exact ⟨packetUnary, approximationRow, sealWindowCont⟩
    ledger_sound := by
      intro _row _rowSource
      exact ⟨packetSig, provenanceUnary, registrationUnary⟩
  }

theorem ComputableRealSource_realup_handoff [AskSetup] [PackageSetup]
    {schedule modulus dyadic regular sealRow transport route provenance registration
      approximationWindow sealWindow packet : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ComputableRealSource schedule modulus dyadic regular sealRow transport route provenance
        registration approximationWindow sealWindow packet bundle pkg ->
      UnaryHistory regular ∧ UnaryHistory sealRow ∧ UnaryHistory sealWindow ∧
        UnaryHistory packet ∧ Cont regular sealRow sealWindow ∧
          Cont approximationWindow sealWindow packet ∧ PkgSig bundle packet pkg := by
  intro source
  obtain ⟨scheduleUnary, modulusUnary, _dyadicUnary, regularUnary, sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _registrationUnary,
    approximationRow, sealWindowRow, packetRow, packetSig⟩ := source
  have approximationUnary : UnaryHistory approximationWindow :=
    unary_cont_closed scheduleUnary modulusUnary approximationRow
  have sealWindowUnary : UnaryHistory sealWindow :=
    unary_cont_closed regularUnary sealUnary sealWindowRow
  have packetUnary : UnaryHistory packet :=
    unary_cont_closed approximationUnary sealWindowUnary packetRow
  exact
    ⟨regularUnary, sealUnary, sealWindowUnary, packetUnary, sealWindowRow,
      packetRow, packetSig⟩

def ComputableRealPacket [AskSetup] [PackageSetup]
    (schedule modulus dyadic regular sealRow transport approximationLedger sealLedger provenance
      nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
    UnaryHistory regular ∧ UnaryHistory sealRow ∧ UnaryHistory nameRow ∧
      Cont schedule modulus transport ∧ Cont dyadic regular approximationLedger ∧
        Cont transport approximationLedger sealLedger ∧ Cont sealLedger nameRow provenance ∧
          PkgSig bundle provenance pkg

theorem ComputableRealPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {schedule modulus dyadic regular sealRow transport approximationLedger sealLedger provenance
      nameRow schedule' modulus' dyadic' regular' sealRow' transport' approximationLedger'
      sealLedger' provenance' nameRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ComputableRealPacket schedule modulus dyadic regular sealRow transport approximationLedger
        sealLedger provenance nameRow bundle pkg ->
      hsame schedule schedule' ->
        hsame modulus modulus' ->
          hsame dyadic dyadic' ->
            hsame regular regular' ->
              hsame sealRow sealRow' ->
                hsame nameRow nameRow' ->
                  Cont schedule' modulus' transport' ->
                    Cont dyadic' regular' approximationLedger' ->
                      Cont transport' approximationLedger' sealLedger' ->
                        Cont sealLedger' nameRow' provenance' ->
                          PkgSig bundle provenance' pkg ->
                            ComputableRealPacket schedule' modulus' dyadic' regular' sealRow'
                                transport' approximationLedger' sealLedger' provenance' nameRow'
                                bundle pkg ∧
                              UnaryHistory dyadic' ∧ UnaryHistory regular' ∧
                                UnaryHistory sealRow' ∧ hsame transport transport' ∧
                                  hsame approximationLedger approximationLedger' ∧
                                    hsame sealLedger sealLedger' := by
  intro packet sameSchedule sameModulus sameDyadic sameRegular sameSeal sameNameRow
    transportRow approximationRow sealLedgerRow provenanceRow provenancePkg
  obtain ⟨scheduleUnary, modulusUnary, dyadicUnary, regularUnary, sealUnary, nameRowUnary,
    transportOld, approximationOld, sealLedgerOld, _provenanceOld, _pkgOld⟩ := packet
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have dyadicUnary' : UnaryHistory dyadic' :=
    unary_transport dyadicUnary sameDyadic
  have regularUnary' : UnaryHistory regular' :=
    unary_transport regularUnary sameRegular
  have sealUnary' : UnaryHistory sealRow' :=
    unary_transport sealUnary sameSeal
  have nameRowUnary' : UnaryHistory nameRow' :=
    unary_transport nameRowUnary sameNameRow
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame sameSchedule sameModulus transportOld transportRow
  have sameApproximation : hsame approximationLedger approximationLedger' :=
    cont_respects_hsame sameDyadic sameRegular approximationOld approximationRow
  have sameSealLedger : hsame sealLedger sealLedger' :=
    cont_respects_hsame sameTransport sameApproximation sealLedgerOld sealLedgerRow
  exact
    ⟨⟨scheduleUnary', modulusUnary', dyadicUnary', regularUnary', sealUnary', nameRowUnary',
        transportRow, approximationRow, sealLedgerRow, provenanceRow, provenancePkg⟩,
      dyadicUnary', regularUnary', sealUnary', sameTransport, sameApproximation,
      sameSealLedger⟩

theorem ComputableRealSourcePacket_effective_window_determinacy [AskSetup] [PackageSetup]
    {stream modulus dyadic regseq «seal» transport routes provenance name endpoint publicRow
      : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ComputableRealSourcePacket stream modulus dyadic regseq «seal» transport routes provenance
        name endpoint bundle pkg ->
      Cont regseq «seal» publicRow ->
        PkgSig bundle publicRow pkg ->
          UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
            UnaryHistory regseq ∧ UnaryHistory «seal» ∧ UnaryHistory publicRow ∧
              Cont regseq «seal» publicRow ∧ PkgSig bundle publicRow pkg := by
  intro packet publicRoute publicPkg
  obtain ⟨streamUnary, modulusUnary, dyadicUnary, regseqUnary, sealUnary,
    _transportRow, _routesRow, _provenanceRow, _endpointRow, _endpointPkg⟩ := packet
  have publicUnary : UnaryHistory publicRow :=
    unary_cont_closed regseqUnary sealUnary publicRoute
  exact
    ⟨streamUnary, modulusUnary, dyadicUnary, regseqUnary, sealUnary, publicUnary,
      publicRoute, publicPkg⟩

theorem ComputableRealSourcePacket_classifier_transport [AskSetup] [PackageSetup]
    {stream modulus dyadic regseq «seal» transport routes provenance name endpoint
      stream' modulus' dyadic' regseq' seal' transport' routes' provenance' name' endpoint' :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ComputableRealSourcePacket stream modulus dyadic regseq «seal» transport routes provenance
        name endpoint bundle pkg ->
      hsame stream stream' ->
      hsame modulus modulus' ->
      hsame dyadic dyadic' ->
      hsame regseq regseq' ->
      hsame «seal» seal' ->
      hsame name name' ->
      Cont stream' modulus' transport' ->
      Cont dyadic' regseq' routes' ->
      Cont transport' routes' provenance' ->
      Cont provenance' name' endpoint' ->
      PkgSig bundle endpoint' pkg ->
      ComputableRealSourcePacket stream' modulus' dyadic' regseq' seal' transport' routes'
        provenance' name' endpoint' bundle pkg ∧ hsame endpoint endpoint' := by
  intro packet sameStream sameModulus sameDyadic sameRegseq sameSeal sameName
    newTransport newRoutes newProvenance newEndpoint newPkg
  have coverage := ComputableRealSourcePacket_ledger_coverage packet
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame sameStream sameModulus coverage.right.right.right.right.right.left
      newTransport
  have sameRoutes : hsame routes routes' :=
    cont_respects_hsame sameDyadic sameRegseq
      coverage.right.right.right.right.right.right.left newRoutes
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameTransport sameRoutes
      coverage.right.right.right.right.right.right.right.left newProvenance
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameName
      coverage.right.right.right.right.right.right.right.right.left newEndpoint
  exact And.intro
    (And.intro
      (unary_transport coverage.left sameStream)
      (And.intro
        (unary_transport coverage.right.left sameModulus)
        (And.intro
          (unary_transport coverage.right.right.left sameDyadic)
          (And.intro
            (unary_transport coverage.right.right.right.left sameRegseq)
            (And.intro
              (unary_transport coverage.right.right.right.right.left sameSeal)
              (And.intro newTransport
                (And.intro newRoutes
                    (And.intro newProvenance
                      (And.intro newEndpoint newPkg)))))))))
    sameEndpoint

theorem ComputableRealPacket_realup_handoff [AskSetup] [PackageSetup]
    {schedule modulus dyadic regular sealRow transport approximationLedger sealLedger provenance
      nameRow realRead publicRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ComputableRealPacket schedule modulus dyadic regular sealRow transport approximationLedger
        sealLedger provenance nameRow bundle pkg ->
      Cont regular sealRow realRead ->
        Cont realRead nameRow publicRow ->
          PkgSig bundle publicRow pkg ->
            UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
              UnaryHistory regular ∧ UnaryHistory sealRow ∧ UnaryHistory realRead ∧
                UnaryHistory publicRow ∧ Cont regular sealRow realRead ∧
                  Cont realRead nameRow publicRow ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle publicRow pkg := by
  intro packet realRoute publicRoute publicPkg
  obtain ⟨scheduleUnary, modulusUnary, dyadicUnary, regularUnary, sealUnary, nameRowUnary,
    _transportRow, _approximationRow, _sealLedgerRow, _provenanceRow, provenancePkg⟩ := packet
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary sealUnary realRoute
  have publicUnary : UnaryHistory publicRow :=
    unary_cont_closed realUnary nameRowUnary publicRoute
  exact
    ⟨scheduleUnary, modulusUnary, dyadicUnary, regularUnary, sealUnary, realUnary,
      publicUnary, realRoute, publicRoute, provenancePkg, publicPkg⟩

theorem ComputableRealSourcePacket_regseqrat_seal_factorization [AskSetup] [PackageSetup]
    {stream modulus dyadic regseq sealRow transport routes provenance name endpoint sealRead
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ComputableRealSourcePacket stream modulus dyadic regseq sealRow transport routes provenance
        name endpoint bundle pkg ->
      UnaryHistory name ->
        Cont regseq sealRow sealRead ->
          Cont sealRead name consumer ->
            PkgSig bundle consumer pkg ->
              UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
                UnaryHistory regseq ∧ UnaryHistory sealRow ∧ UnaryHistory name ∧
                  UnaryHistory sealRead ∧ UnaryHistory consumer ∧
                    Cont stream modulus transport ∧ Cont dyadic regseq routes ∧
                      Cont transport routes provenance ∧ Cont provenance name endpoint ∧
                        Cont regseq sealRow sealRead ∧ Cont sealRead name consumer ∧
                          PkgSig bundle endpoint pkg ∧ PkgSig bundle consumer pkg := by
  intro packet nameUnary sealReadRow consumerRow consumerPkg
  obtain ⟨streamUnary, modulusUnary, dyadicUnary, regseqUnary, sealUnary, streamModulusRow,
    dyadicRegseqRow, transportRoutesRow, provenanceNameEndpoint, endpointPkg⟩ := packet
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqUnary sealUnary sealReadRow
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed sealReadUnary nameUnary consumerRow
  exact
    ⟨streamUnary, modulusUnary, dyadicUnary, regseqUnary, sealUnary, nameUnary,
      sealReadUnary, consumerUnary, streamModulusRow, dyadicRegseqRow, transportRoutesRow,
      provenanceNameEndpoint, sealReadRow, consumerRow, endpointPkg, consumerPkg⟩

end BEDC.Derived.ComputableRealUp
