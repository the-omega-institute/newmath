import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BoundedMonotoneCauchyWitnessCarrier [AskSetup] [PackageSetup]
    (source regular schedule witness ledger trap sealRow transport route provenance
      localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
    UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
      UnaryHistory sealRow ∧ UnaryHistory provenance ∧ Cont source schedule regular ∧
        Cont regular witness trap ∧ Cont trap sealRow route ∧ Cont transport localCert route ∧
          Cont route provenance sealRow ∧ PkgSig bundle provenance pkg

theorem BoundedMonotoneCauchyWitnessCarrier_tail_seal_synchronization [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule tailRead →
        Cont tailRead witness sealRead →
          Cont sealRead sealRow route →
            PkgSig bundle route pkg →
              UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory witness ∧
                UnaryHistory sealRow ∧ UnaryHistory tailRead ∧ UnaryHistory sealRead ∧
                  Cont source schedule tailRead ∧ Cont tailRead witness sealRead ∧
                    Cont sealRead sealRow route ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle route pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleTail tailWitnessSeal sealRowRoute routePkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, _ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleTail
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary witnessUnary tailWitnessSeal
  exact
    ⟨sourceUnary, scheduleUnary, witnessUnary, sealUnary, tailUnary, sealReadUnary,
      sourceScheduleTail, tailWitnessSeal, sealRowRoute, provenancePkg, routePkg⟩

theorem BoundedMonotoneCauchyWitnessCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row sealRow ∧
              BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap
                sealRow transport route provenance localCert bundle pkg)
          (fun row : BHist =>
            hsame row sealRow ∧ UnaryHistory regular ∧ UnaryHistory witness ∧ UnaryHistory trap)
          (fun row : BHist => hsame row sealRow ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
          UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧ UnaryHistory sealRow ∧
            Cont source schedule regular ∧ Cont regular witness trap ∧ Cont trap sealRow route ∧
              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont PkgSig SemanticNameCert hsame
  intro carrier
  have carrierFull :
      BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg :=
    carrier
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, pkgSig⟩ := carrier
  have sourceAtSeal :
      hsame sealRow sealRow ∧
        BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
          transport route provenance localCert bundle pkg :=
    And.intro (hsame_refl sealRow) carrierFull
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row sealRow ∧
              BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap
                sealRow transport route provenance localCert bundle pkg)
          (fun row : BHist =>
            hsame row sealRow ∧ UnaryHistory regular ∧ UnaryHistory witness ∧ UnaryHistory trap)
          (fun row : BHist => hsame row sealRow ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRow sourceAtSeal
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        constructor
        · exact hsame_trans (hsame_symm sameRows) source.left
        · exact source.right
    }
    pattern_sound := by
      intro row source
      exact And.intro source.left
        (And.intro regularUnary (And.intro witnessUnary trapUnary))
    ledger_sound := by
      intro row source
      exact And.intro source.left pkgSig
  }
  exact And.intro cert
    (And.intro sourceUnary
      (And.intro regularUnary
        (And.intro scheduleUnary
          (And.intro witnessUnary
            (And.intro ledgerUnary
              (And.intro trapUnary
                (And.intro sealUnary
                  (And.intro sourceScheduleRegular
                    (And.intro regularWitnessTrap
                      (And.intro trapSealRoute pkgSig))))))))))

theorem BoundedMonotoneCauchyWitnessCarrier_convergence_seal_source [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance
      localCert convergenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont sealRow provenance convergenceRead ->
        PkgSig bundle convergenceRead pkg ->
          UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
            UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
              UnaryHistory sealRow ∧ UnaryHistory provenance ∧
                UnaryHistory convergenceRead ∧ Cont source schedule regular ∧
                  Cont regular witness trap ∧ Cont trap sealRow route ∧
                    Cont sealRow provenance convergenceRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle convergenceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier convergenceRoute convergencePkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have convergenceUnary : UnaryHistory convergenceRead :=
    unary_cont_closed sealUnary provenanceUnary convergenceRoute
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      provenanceUnary, convergenceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
      convergenceRoute, provenancePkg, convergencePkg⟩

theorem BoundedMonotoneCauchyWitnessCarrier_completion_consumer_nonescape [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      envelopeRead finiteRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule envelopeRead →
        Cont envelopeRead regular finiteRead →
          Cont finiteRead sealRow completionRead →
            PkgSig bundle completionRead pkg →
              UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                  UnaryHistory sealRow ∧ UnaryHistory provenance ∧ UnaryHistory envelopeRead ∧
                    UnaryHistory finiteRead ∧ UnaryHistory completionRead ∧
                      Cont source schedule envelopeRead ∧
                        Cont envelopeRead regular finiteRead ∧
                          Cont finiteRead sealRow completionRead ∧
                            Cont source schedule regular ∧ Cont regular witness trap ∧
                              Cont trap sealRow route ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier envelopeRoute finiteRoute completionRoute completionPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed sourceUnary scheduleUnary envelopeRoute
  have finiteUnary : UnaryHistory finiteRead :=
    unary_cont_closed envelopeUnary regularUnary finiteRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed finiteUnary sealUnary completionRoute
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      provenanceUnary, envelopeUnary, finiteUnary, completionUnary, envelopeRoute, finiteRoute,
      completionRoute, sourceScheduleRegular, regularWitnessTrap, trapSealRoute, provenancePkg,
      completionPkg⟩

theorem BoundedMonotoneCauchyWitnessCarrier_tail_envelope_public_export
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      envelopeRead budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule envelopeRead ->
        Cont envelopeRead ledger budgetRead ->
          PkgSig bundle budgetRead pkg ->
            UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
              UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                UnaryHistory sealRow ∧ UnaryHistory envelopeRead ∧ UnaryHistory budgetRead ∧
                  Cont source schedule envelopeRead ∧ Cont envelopeRead ledger budgetRead ∧
                    Cont source schedule regular ∧ Cont regular witness trap ∧
                      Cont trap sealRow route ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle budgetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier envelopeRoute budgetRoute budgetPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed sourceUnary scheduleUnary envelopeRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed envelopeUnary ledgerUnary budgetRoute
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      envelopeUnary, budgetUnary, envelopeRoute, budgetRoute, sourceScheduleRegular,
      regularWitnessTrap, trapSealRoute, provenancePkg, budgetPkg⟩

theorem BoundedMonotoneCauchyWitnessCarrier_root_extraction [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source regular rootRead →
        Cont rootRead witness sealRow →
          PkgSig bundle rootRead pkg →
            UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
              UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                UnaryHistory sealRow ∧ UnaryHistory provenance ∧ UnaryHistory rootRead ∧
                  Cont source regular rootRead ∧ Cont rootRead witness sealRow ∧
                    Cont trap sealRow route ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceRegularRoot rootWitnessSeal rootPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed sourceUnary regularUnary sourceRegularRoot
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      provenanceUnary, rootUnary, sourceRegularRoot, rootWitnessSeal, trapSealRoute,
      provenancePkg, rootPkg⟩

theorem BoundedMonotoneCauchyWitnessCarrier_convergence_seal_input_package [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      envelopeRead criterionRead convergenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule envelopeRead →
        Cont envelopeRead witness criterionRead →
          Cont criterionRead sealRow convergenceRead →
            PkgSig bundle convergenceRead pkg →
              UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                  UnaryHistory sealRow ∧ UnaryHistory provenance ∧ UnaryHistory envelopeRead ∧
                    UnaryHistory criterionRead ∧ UnaryHistory convergenceRead ∧
                      Cont source schedule envelopeRead ∧
                        Cont envelopeRead witness criterionRead ∧
                          Cont criterionRead sealRow convergenceRead ∧
                            Cont source schedule regular ∧ Cont regular witness trap ∧
                              Cont trap sealRow route ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle convergenceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier envelopeRoute criterionRoute convergenceRoute convergencePkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed sourceUnary scheduleUnary envelopeRoute
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed envelopeUnary witnessUnary criterionRoute
  have convergenceUnary : UnaryHistory convergenceRead :=
    unary_cont_closed criterionUnary sealUnary convergenceRoute
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      provenanceUnary, envelopeUnary, criterionUnary, convergenceUnary, envelopeRoute,
      criterionRoute, convergenceRoute, sourceScheduleRegular, regularWitnessTrap,
      trapSealRoute, provenancePkg, convergencePkg⟩

theorem BoundedMonotoneCauchyWitnessCarrier_seal_input_transport [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      source' regular' schedule' witness' ledger' trap' sealRow' transport' route' provenance'
      localCert' envelopeRead' criterionRead' convergenceRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      hsame source source' ->
      hsame regular regular' ->
      hsame schedule schedule' ->
      hsame witness witness' ->
      hsame ledger ledger' ->
      hsame trap trap' ->
      hsame sealRow sealRow' ->
      hsame transport transport' ->
      hsame route route' ->
      hsame provenance provenance' ->
      hsame localCert localCert' ->
      Cont source' schedule' envelopeRead' ->
      Cont envelopeRead' witness' criterionRead' ->
      Cont criterionRead' sealRow' convergenceRead' ->
      PkgSig bundle convergenceRead' pkg ->
        UnaryHistory source' ∧ UnaryHistory regular' ∧ UnaryHistory schedule' ∧
          UnaryHistory witness' ∧ UnaryHistory ledger' ∧ UnaryHistory trap' ∧
            UnaryHistory sealRow' ∧ UnaryHistory provenance' ∧ UnaryHistory envelopeRead' ∧
              UnaryHistory criterionRead' ∧ UnaryHistory convergenceRead' ∧
                Cont source' schedule' envelopeRead' ∧
                  Cont envelopeRead' witness' criterionRead' ∧
                    Cont criterionRead' sealRow' convergenceRead' ∧
                      PkgSig bundle convergenceRead' pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg UnaryHistory
  intro carrier sourceSame regularSame scheduleSame witnessSame ledgerSame trapSame sealSame
    _transportSame _routeSame provenanceSame _localCertSame envelopeRoute criterionRoute
    convergenceRoute convergencePkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, _provenancePkg⟩ := carrier
  cases sourceSame
  cases regularSame
  cases scheduleSame
  cases witnessSame
  cases ledgerSame
  cases trapSame
  cases sealSame
  cases provenanceSame
  have envelopeUnary : UnaryHistory envelopeRead' :=
    unary_cont_closed sourceUnary scheduleUnary envelopeRoute
  have criterionUnary : UnaryHistory criterionRead' :=
    unary_cont_closed envelopeUnary witnessUnary criterionRoute
  have convergenceUnary : UnaryHistory convergenceRead' :=
    unary_cont_closed criterionUnary sealUnary convergenceRoute
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
      sealUnary, provenanceUnary, envelopeUnary, criterionUnary, convergenceUnary,
      envelopeRoute, criterionRoute, convergenceRoute, convergencePkg⟩

theorem BoundedMonotoneCauchyWitnessCarrier_criterion_tail_factorization
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      criterionTail convergenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont regular witness criterionTail ->
        Cont criterionTail sealRow convergenceRead ->
          PkgSig bundle convergenceRead pkg ->
            UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
              UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                UnaryHistory sealRow ∧ UnaryHistory criterionTail ∧
                  UnaryHistory convergenceRead ∧ Cont source schedule regular ∧
                    Cont regular witness criterionTail ∧
                      Cont criterionTail sealRow convergenceRead ∧ Cont trap sealRow route ∧
                        PkgSig bundle provenance pkg ∧
                          PkgSig bundle convergenceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier regularWitnessCriterion criterionSealConvergence convergencePkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, _regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have criterionUnary : UnaryHistory criterionTail :=
    unary_cont_closed regularUnary witnessUnary regularWitnessCriterion
  have convergenceUnary : UnaryHistory convergenceRead :=
    unary_cont_closed criterionUnary sealUnary criterionSealConvergence
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      criterionUnary, convergenceUnary, sourceScheduleRegular, regularWitnessCriterion,
      criterionSealConvergence, trapSealRoute, provenancePkg, convergencePkg⟩

theorem BoundedMonotoneCauchyWitnessCarrier_root_seal_route_exhaustion
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      rootRead limitRead monotoneRead sealExhaustRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source regular rootRead →
        Cont rootRead witness sealRow →
          Cont sealRow provenance limitRead →
            Cont source schedule monotoneRead →
              Cont monotoneRead trap sealExhaustRead →
                PkgSig bundle rootRead pkg →
                  PkgSig bundle limitRead pkg →
                    PkgSig bundle sealExhaustRead pkg →
                      UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                        UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                          UnaryHistory sealRow ∧ UnaryHistory provenance ∧
                            UnaryHistory rootRead ∧ UnaryHistory limitRead ∧
                              UnaryHistory monotoneRead ∧ UnaryHistory sealExhaustRead ∧
                                Cont source regular rootRead ∧
                                  Cont rootRead witness sealRow ∧
                                    Cont sealRow provenance limitRead ∧
                                      Cont source schedule monotoneRead ∧
                                        Cont monotoneRead trap sealExhaustRead ∧
                                          Cont trap sealRow route ∧
                                            PkgSig bundle provenance pkg ∧
                                              PkgSig bundle rootRead pkg ∧
                                                PkgSig bundle limitRead pkg ∧
                                                  PkgSig bundle sealExhaustRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceRegularRoot rootWitnessSeal sealProvenanceLimit sourceScheduleMonotone
    monotoneTrapSealExhaust rootPkg limitPkg sealExhaustPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed sourceUnary regularUnary sourceRegularRoot
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed sealUnary provenanceUnary sealProvenanceLimit
  have monotoneUnary : UnaryHistory monotoneRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleMonotone
  have sealExhaustUnary : UnaryHistory sealExhaustRead :=
    unary_cont_closed monotoneUnary trapUnary monotoneTrapSealExhaust
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      provenanceUnary, rootUnary, limitUnary, monotoneUnary, sealExhaustUnary,
      sourceRegularRoot, rootWitnessSeal, sealProvenanceLimit, sourceScheduleMonotone,
      monotoneTrapSealExhaust, trapSealRoute, provenancePkg, rootPkg, limitPkg,
      sealExhaustPkg⟩

theorem BoundedMonotoneCauchyWitnessCarrier_completion_consumer_apartness_budget
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      envelopeRead apartnessRead preSealRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule envelopeRead ->
        Cont envelopeRead ledger apartnessRead ->
          Cont apartnessRead trap preSealRead ->
            Cont preSealRead sealRow completionRead ->
              PkgSig bundle completionRead pkg ->
                UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory ledger ∧
                  UnaryHistory trap ∧ UnaryHistory sealRow ∧ UnaryHistory envelopeRead ∧
                    UnaryHistory apartnessRead ∧ UnaryHistory preSealRead ∧
                      UnaryHistory completionRead ∧ Cont source schedule envelopeRead ∧
                        Cont envelopeRead ledger apartnessRead ∧
                          Cont apartnessRead trap preSealRead ∧
                            Cont preSealRead sealRow completionRead ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleEnvelope envelopeLedgerApartness apartnessTrapPreSeal
    preSealSealCompletion completionPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, _witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ :=
    carrier
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleEnvelope
  have apartnessUnary : UnaryHistory apartnessRead :=
    unary_cont_closed envelopeUnary ledgerUnary envelopeLedgerApartness
  have preSealUnary : UnaryHistory preSealRead :=
    unary_cont_closed apartnessUnary trapUnary apartnessTrapPreSeal
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed preSealUnary sealUnary preSealSealCompletion
  exact
    ⟨sourceUnary, scheduleUnary, ledgerUnary, trapUnary, sealUnary, envelopeUnary,
      apartnessUnary, preSealUnary, completionUnary, sourceScheduleEnvelope,
      envelopeLedgerApartness, apartnessTrapPreSeal, preSealSealCompletion, provenancePkg,
      completionPkg⟩

theorem BoundedMonotoneCauchyWitnessCarrier_root_monotone_window_totality
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      windowRead witnessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule windowRead →
        Cont windowRead regular witnessRead →
          PkgSig bundle witnessRead pkg →
            UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
              UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                UnaryHistory sealRow ∧ UnaryHistory provenance ∧ UnaryHistory windowRead ∧
                  UnaryHistory witnessRead ∧ Cont source schedule windowRead ∧
                    Cont windowRead regular witnessRead ∧ Cont source schedule regular ∧
                      Cont regular witness trap ∧ Cont trap sealRow route ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle witnessRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleWindow windowRegularWitness witnessPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindow
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed windowUnary regularUnary windowRegularWitness
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      provenanceUnary, windowUnary, witnessReadUnary, sourceScheduleWindow,
      windowRegularWitness, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
      provenancePkg, witnessPkg⟩

theorem BoundedMonotoneCauchyWitnessCarrier_tail_seal_row_determinacy
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert tailA
      tailB readA readB : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg → Cont source schedule tailA →
      Cont source schedule tailB → Cont tailA sealRow readA → Cont tailB sealRow readB →
        PkgSig bundle readA pkg → PkgSig bundle readB pkg →
          UnaryHistory tailA ∧ UnaryHistory tailB ∧ UnaryHistory readA ∧ UnaryHistory readB ∧
            hsame tailA tailB ∧ hsame readA readB ∧ Cont tailA sealRow readA ∧
              Cont tailB sealRow readB ∧ PkgSig bundle readA pkg ∧
                PkgSig bundle readB pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sourceScheduleTailA sourceScheduleTailB tailSealReadA tailSealReadB readPkgA
    readPkgB
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, _witnessUnary, _ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, _provenancePkg⟩ := carrier
  have tailUnaryA : UnaryHistory tailA :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleTailA
  have tailUnaryB : UnaryHistory tailB :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleTailB
  have readUnaryA : UnaryHistory readA := unary_cont_closed tailUnaryA sealUnary tailSealReadA
  have readUnaryB : UnaryHistory readB := unary_cont_closed tailUnaryB sealUnary tailSealReadB
  have sameTail : hsame tailA tailB :=
    cont_respects_hsame (hsame_refl source) (hsame_refl schedule) sourceScheduleTailA
      sourceScheduleTailB
  have sameRead : hsame readA readB :=
    cont_respects_hsame sameTail (hsame_refl sealRow) tailSealReadA tailSealReadB
  exact ⟨tailUnaryA, tailUnaryB, readUnaryA, readUnaryB, sameTail, sameRead, tailSealReadA,
    tailSealReadB, readPkgA, readPkgB⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
