import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

/-!
# CauchyCriterionUp finite carrier surface.
-/

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

def CauchyCriterionCarrier [AskSetup] [PackageSetup]
    (window modulus tolerance ledger regseq realSeal transport route provenance localCert
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory window ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
    UnaryHistory ledger ∧ UnaryHistory regseq ∧ UnaryHistory realSeal ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory localCert ∧ UnaryHistory endpoint ∧
          Cont window modulus tolerance ∧ Cont tolerance ledger regseq ∧
            Cont regseq realSeal transport ∧ Cont transport localCert route ∧
              Cont route provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem CauchyCriterionCarrier_modulus_threshold_stability [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      window' modulus' tolerance' ledger' regseq' realSeal' transport' route' provenance'
      localCert' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      hsame window window' ->
        hsame modulus modulus' ->
          hsame ledger ledger' ->
            hsame realSeal realSeal' ->
              hsame provenance provenance' ->
                hsame localCert localCert' ->
                  Cont window' modulus' tolerance' ->
                    Cont tolerance' ledger' regseq' ->
                      Cont regseq' realSeal' transport' ->
                        Cont transport' localCert' route' ->
                          Cont route' provenance' endpoint' ->
                            PkgSig bundle endpoint' pkg ->
                              CauchyCriterionCarrier window' modulus' tolerance' ledger' regseq'
                                  realSeal' transport' route' provenance' localCert' endpoint'
                                  bundle pkg ∧
                                hsame tolerance tolerance' ∧
                                  hsame regseq regseq' ∧
                                    hsame transport transport' ∧
                                      hsame route route' ∧ hsame endpoint endpoint' := by
  intro carrier sameWindow sameModulus sameLedger sameRealSeal sameProvenance sameLocalCert
    toleranceRow' regseqRow' transportRow' routeRow' endpointRow' pkgSig'
  rcases carrier with
    ⟨windowUnary, modulusUnary, _toleranceUnary, ledgerUnary, _regseqUnary, realSealUnary,
      _transportUnary, _routeUnary, provenanceUnary, localCertUnary, _endpointUnary,
      toleranceRow, regseqRow, transportRow, routeRow, endpointRow, _pkgSig⟩
  have windowUnary' : UnaryHistory window' :=
    unary_transport windowUnary sameWindow
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_transport ledgerUnary sameLedger
  have realSealUnary' : UnaryHistory realSeal' :=
    unary_transport realSealUnary sameRealSeal
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have localCertUnary' : UnaryHistory localCert' :=
    unary_transport localCertUnary sameLocalCert
  have toleranceUnary' : UnaryHistory tolerance' :=
    unary_cont_closed windowUnary' modulusUnary' toleranceRow'
  have regseqUnary' : UnaryHistory regseq' :=
    unary_cont_closed toleranceUnary' ledgerUnary' regseqRow'
  have transportUnary' : UnaryHistory transport' :=
    unary_cont_closed regseqUnary' realSealUnary' transportRow'
  have routeUnary' : UnaryHistory route' :=
    unary_cont_closed transportUnary' localCertUnary' routeRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed routeUnary' provenanceUnary' endpointRow'
  have sameTolerance : hsame tolerance tolerance' :=
    cont_respects_hsame sameWindow sameModulus toleranceRow toleranceRow'
  have sameRegseq : hsame regseq regseq' :=
    cont_respects_hsame sameTolerance sameLedger regseqRow regseqRow'
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame sameRegseq sameRealSeal transportRow transportRow'
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameTransport sameLocalCert routeRow routeRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameRoute sameProvenance endpointRow endpointRow'
  have targetCarrier :
      CauchyCriterionCarrier window' modulus' tolerance' ledger' regseq' realSeal'
        transport' route' provenance' localCert' endpoint' bundle pkg :=
    ⟨windowUnary', modulusUnary', toleranceUnary', ledgerUnary', regseqUnary', realSealUnary',
      transportUnary', routeUnary', provenanceUnary', localCertUnary', endpointUnary',
      toleranceRow', regseqRow', transportRow', routeRow', endpointRow', pkgSig'⟩
  exact And.intro targetCarrier
    (And.intro sameTolerance
      (And.intro sameRegseq
        (And.intro sameTransport (And.intro sameRoute sameEndpoint))))

theorem CauchyCriterionRoute_precision_endpoint_closure
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert
      endpoint : BHist} :
    UnaryHistory window ->
      UnaryHistory modulus ->
        UnaryHistory ledger ->
          UnaryHistory realSeal ->
            UnaryHistory localCert ->
              UnaryHistory provenance ->
                Cont window modulus tolerance ->
                  Cont tolerance ledger regseq ->
                    Cont regseq realSeal transport ->
                      Cont transport localCert route ->
                        Cont route provenance endpoint ->
                          UnaryHistory tolerance ∧ UnaryHistory regseq ∧
                            UnaryHistory transport ∧ UnaryHistory route ∧
                              UnaryHistory endpoint := by
  intro windowUnary modulusUnary ledgerUnary realSealUnary localCertUnary provenanceUnary
    toleranceRow regseqRow transportRow routeRow endpointRow
  have toleranceUnary : UnaryHistory tolerance :=
    unary_cont_closed windowUnary modulusUnary toleranceRow
  have regseqUnary : UnaryHistory regseq :=
    unary_cont_closed toleranceUnary ledgerUnary regseqRow
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed regseqUnary realSealUnary transportRow
  have routeUnary : UnaryHistory route :=
    unary_cont_closed transportUnary localCertUnary routeRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed routeUnary provenanceUnary endpointRow
  exact And.intro toleranceUnary
    (And.intro regseqUnary
      (And.intro transportUnary (And.intro routeUnary endpointUnary)))

def CauchyCriterionNameCertCarrier [AskSetup] [PackageSetup]
    (window modulus tail tolerance sealRow transportRow route provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Cont window modulus tail ∧
    Cont tail tolerance transportRow ∧
      Cont transportRow route provenance ∧
        Cont provenance localCert sealRow ∧
          PkgSig bundle provenance pkg ∧ hsame sealRow tail ∧ hsame sealRow provenance

theorem CauchyCriterionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {window modulus tail tolerance sealRow transportRow route provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionNameCertCarrier window modulus tail tolerance sealRow transportRow route
        provenance localCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyCriterionNameCertCarrier window modulus tail tolerance sealRow transportRow route
            provenance localCert bundle pkg ∧ hsame row sealRow)
        (fun row : BHist =>
          CauchyCriterionNameCertCarrier window modulus tail tolerance sealRow transportRow route
            provenance localCert bundle pkg ∧ hsame row tail)
        (fun row : BHist =>
          CauchyCriterionNameCertCarrier window modulus tail tolerance sealRow transportRow route
            provenance localCert bundle pkg ∧ hsame row provenance)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sealRow (And.intro carrier (hsame_refl sealRow))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact And.intro source.left
        (hsame_trans source.right source.left.right.right.right.right.right.left)
    ledger_sound := by
      intro _row source
      exact And.intro source.left
        (hsame_trans source.right source.left.right.right.right.right.right.right)
  }

theorem CauchyCriterionCarrier_tail_bound_real_seal [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont ledger realSeal consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory window ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
            UnaryHistory ledger ∧ UnaryHistory realSeal ∧ UnaryHistory consumer ∧
              Cont window modulus tolerance ∧ Cont tolerance ledger regseq ∧
                Cont ledger realSeal consumer ∧ PkgSig bundle endpoint pkg ∧
                  PkgSig bundle consumer pkg := by
  intro carrier ledgerRealSealConsumer consumerPkg
  obtain ⟨windowUnary, modulusUnary, toleranceUnary, ledgerUnary, _regseqUnary, realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    windowModulusTolerance, toleranceLedgerRegseq, _regseqRealSealTransport,
    _transportLocalRoute, _routeProvenanceEndpoint, endpointPkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed ledgerUnary realSealUnary ledgerRealSealConsumer
  exact
    ⟨windowUnary, modulusUnary, toleranceUnary, ledgerUnary, realSealUnary, consumerUnary,
      windowModulusTolerance, toleranceLedgerRegseq, ledgerRealSealConsumer, endpointPkg,
      consumerPkg⟩

theorem CauchyCriterionCarrier_scoped_tail_seal_transport [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont endpoint localCert scopedRead ->
        PkgSig bundle scopedRead pkg ->
          UnaryHistory window ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
            UnaryHistory ledger ∧ UnaryHistory regseq ∧ UnaryHistory realSeal ∧
              UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory endpoint ∧
                UnaryHistory scopedRead ∧ Cont window modulus tolerance ∧
                  Cont tolerance ledger regseq ∧ Cont regseq realSeal transport ∧
                    Cont transport localCert route ∧ Cont route provenance endpoint ∧
                      Cont endpoint localCert scopedRead ∧ PkgSig bundle endpoint pkg ∧
                        PkgSig bundle scopedRead pkg := by
  intro carrier endpointLocalCertScopedRead scopedReadPkg
  obtain ⟨windowUnary, modulusUnary, toleranceUnary, ledgerUnary, regseqUnary,
    realSealUnary, transportUnary, routeUnary, _provenanceUnary, localCertUnary,
    endpointUnary, windowModulusTolerance, toleranceLedgerRegseq, regseqRealSealTransport,
    transportLocalCertRoute, routeProvenanceEndpoint, endpointPkg⟩ := carrier
  have scopedReadUnary : UnaryHistory scopedRead :=
    unary_cont_closed endpointUnary localCertUnary endpointLocalCertScopedRead
  exact
    ⟨windowUnary, modulusUnary, toleranceUnary, ledgerUnary, regseqUnary, realSealUnary,
      transportUnary, routeUnary, endpointUnary, scopedReadUnary, windowModulusTolerance,
      toleranceLedgerRegseq, regseqRealSealTransport, transportLocalCertRoute,
      routeProvenanceEndpoint, endpointLocalCertScopedRead, endpointPkg, scopedReadPkg⟩

theorem CauchyCriterionCarrier_dyadic_tail_ledger_exactness [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      tailConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont ledger provenance tailConsumer ->
        PkgSig bundle tailConsumer pkg ->
          UnaryHistory modulus ∧ UnaryHistory tolerance ∧ UnaryHistory ledger ∧
            UnaryHistory tailConsumer ∧ Cont window modulus tolerance ∧
              Cont tolerance ledger regseq ∧ Cont ledger provenance tailConsumer ∧
                PkgSig bundle endpoint pkg ∧ PkgSig bundle tailConsumer pkg := by
  intro carrier ledgerProvenanceTailConsumer tailConsumerPkg
  obtain ⟨_windowUnary, modulusUnary, toleranceUnary, ledgerUnary, _regseqUnary,
    _realSealUnary, _transportUnary, _routeUnary, provenanceUnary, _localCertUnary,
    _endpointUnary, windowModulusTolerance, toleranceLedgerRegseq, _regseqRealSealTransport,
    _transportLocalRoute, _routeProvenanceEndpoint, endpointPkg⟩ := carrier
  have tailConsumerUnary : UnaryHistory tailConsumer :=
    unary_cont_closed ledgerUnary provenanceUnary ledgerProvenanceTailConsumer
  exact
    ⟨modulusUnary, toleranceUnary, ledgerUnary, tailConsumerUnary, windowModulusTolerance,
      toleranceLedgerRegseq, ledgerProvenanceTailConsumer, endpointPkg, tailConsumerPkg⟩

theorem CauchyCriterionCarrier_regseqrat_handoff_exhaustion [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont regseq realSeal handoff ->
        PkgSig bundle handoff pkg ->
          UnaryHistory window ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
            UnaryHistory ledger ∧ UnaryHistory regseq ∧ UnaryHistory realSeal ∧
              UnaryHistory handoff ∧ Cont window modulus tolerance ∧
                Cont tolerance ledger regseq ∧ Cont regseq realSeal handoff ∧
                  PkgSig bundle endpoint pkg ∧ PkgSig bundle handoff pkg := by
  intro carrier regseqRealSealHandoff handoffPkg
  obtain ⟨windowUnary, modulusUnary, toleranceUnary, ledgerUnary, regseqUnary, realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    windowModulusTolerance, toleranceLedgerRegseq, _regseqRealSealTransport,
    _transportLocalRoute, _routeProvenanceEndpoint, endpointPkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed regseqUnary realSealUnary regseqRealSealHandoff
  exact
    ⟨windowUnary, modulusUnary, toleranceUnary, ledgerUnary, regseqUnary, realSealUnary,
      handoffUnary, windowModulusTolerance, toleranceLedgerRegseq, regseqRealSealHandoff,
      endpointPkg, handoffPkg⟩

theorem CauchyCriterionCarrier_real_seal_scope [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      sealRead scopedSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont ledger realSeal sealRead ->
        Cont sealRead provenance scopedSeal ->
          PkgSig bundle scopedSeal pkg ->
            UnaryHistory sealRead ∧ UnaryHistory scopedSeal ∧ Cont window modulus tolerance ∧
              Cont tolerance ledger regseq ∧ Cont ledger realSeal sealRead ∧
                Cont sealRead provenance scopedSeal ∧ PkgSig bundle endpoint pkg ∧
                  PkgSig bundle scopedSeal pkg := by
  intro carrier ledgerRealSealSealRead sealReadProvenanceScopedSeal scopedSealPkg
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, ledgerUnary, _regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, provenanceUnary, _localCertUnary,
    _endpointUnary, windowModulusTolerance, toleranceLedgerRegseq, _regseqRealSealTransport,
    _transportLocalCertRoute, _routeProvenanceEndpoint, endpointPkg⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed ledgerUnary realSealUnary ledgerRealSealSealRead
  have scopedSealUnary : UnaryHistory scopedSeal :=
    unary_cont_closed sealReadUnary provenanceUnary sealReadProvenanceScopedSeal
  exact
    ⟨sealReadUnary, scopedSealUnary, windowModulusTolerance, toleranceLedgerRegseq,
      ledgerRealSealSealRead, sealReadProvenanceScopedSeal, endpointPkg, scopedSealPkg⟩

theorem CauchyCriterionCarrier_tail_budget_scope [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      tailConsumer handoff sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont ledger provenance tailConsumer ->
        Cont regseq realSeal handoff ->
          Cont ledger realSeal sealRead ->
            PkgSig bundle tailConsumer pkg ->
              PkgSig bundle handoff pkg ->
                PkgSig bundle sealRead pkg ->
                  UnaryHistory modulus ∧ UnaryHistory tolerance ∧ UnaryHistory ledger ∧
                    UnaryHistory tailConsumer ∧ UnaryHistory handoff ∧ UnaryHistory sealRead ∧
                      Cont window modulus tolerance ∧ Cont tolerance ledger regseq ∧
                        Cont ledger provenance tailConsumer ∧ Cont regseq realSeal handoff ∧
                          Cont ledger realSeal sealRead ∧ PkgSig bundle endpoint pkg ∧
                            PkgSig bundle tailConsumer pkg ∧ PkgSig bundle handoff pkg ∧
                              PkgSig bundle sealRead pkg := by
  intro carrier ledgerProvenanceTailConsumer regseqRealSealHandoff ledgerRealSealSealRead
    tailConsumerPkg handoffPkg sealReadPkg
  obtain ⟨_windowUnary, modulusUnary, toleranceUnary, ledgerUnary, regseqUnary, realSealUnary,
    _transportUnary, _routeUnary, provenanceUnary, _localCertUnary, _endpointUnary,
    windowModulusTolerance, toleranceLedgerRegseq, _regseqRealSealTransport,
    _transportLocalCertRoute, _routeProvenanceEndpoint, endpointPkg⟩ := carrier
  have tailConsumerUnary : UnaryHistory tailConsumer :=
    unary_cont_closed ledgerUnary provenanceUnary ledgerProvenanceTailConsumer
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed regseqUnary realSealUnary regseqRealSealHandoff
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed ledgerUnary realSealUnary ledgerRealSealSealRead
  exact
    ⟨modulusUnary, toleranceUnary, ledgerUnary, tailConsumerUnary, handoffUnary,
      sealReadUnary, windowModulusTolerance, toleranceLedgerRegseq,
      ledgerProvenanceTailConsumer, regseqRealSealHandoff, ledgerRealSealSealRead,
      endpointPkg, tailConsumerPkg, handoffPkg, sealReadPkg⟩

theorem CauchyCriterionCarrier_tail_budget_seal_determinacy [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      sealRead sealRead' scopedSeal scopedSeal' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont ledger realSeal sealRead ->
        Cont ledger realSeal sealRead' ->
          Cont sealRead provenance scopedSeal ->
            Cont sealRead' provenance scopedSeal' ->
              PkgSig bundle scopedSeal pkg ->
                PkgSig bundle scopedSeal' pkg ->
                  hsame sealRead sealRead' ∧ hsame scopedSeal scopedSeal' ∧
                    UnaryHistory scopedSeal ∧ UnaryHistory scopedSeal' := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro carrier ledgerRealSealSealRead ledgerRealSealSealRead'
    sealReadProvenanceScopedSeal sealReadProvenanceScopedSeal' _scopedSealPkg
    _scopedSealPkg'
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, ledgerUnary, _regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, provenanceUnary, _localCertUnary,
    _endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
    _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
    _endpointPkg⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed ledgerUnary realSealUnary ledgerRealSealSealRead
  have sealReadUnary' : UnaryHistory sealRead' :=
    unary_cont_closed ledgerUnary realSealUnary ledgerRealSealSealRead'
  have scopedSealUnary : UnaryHistory scopedSeal :=
    unary_cont_closed sealReadUnary provenanceUnary sealReadProvenanceScopedSeal
  have scopedSealUnary' : UnaryHistory scopedSeal' :=
    unary_cont_closed sealReadUnary' provenanceUnary sealReadProvenanceScopedSeal'
  have sameSealRead : hsame sealRead sealRead' :=
    cont_respects_hsame (hsame_refl ledger) (hsame_refl realSeal)
      ledgerRealSealSealRead ledgerRealSealSealRead'
  have sameScopedSeal : hsame scopedSeal scopedSeal' :=
    cont_respects_hsame sameSealRead (hsame_refl provenance) sealReadProvenanceScopedSeal
      sealReadProvenanceScopedSeal'
  exact ⟨sameSealRead, sameScopedSeal, scopedSealUnary, scopedSealUnary'⟩

theorem CauchyCriterionCarrier_modulus_tail_consumer_exactness [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      consumer consumer' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont ledger realSeal consumer ->
        Cont ledger realSeal consumer' ->
          PkgSig bundle consumer pkg ->
            PkgSig bundle consumer' pkg ->
              UnaryHistory consumer ∧ UnaryHistory consumer' ∧ hsame consumer consumer' ∧
                PkgSig bundle endpoint pkg ∧ PkgSig bundle consumer pkg ∧
                  PkgSig bundle consumer' pkg := by
  intro carrier ledgerRealSealConsumer ledgerRealSealConsumer' consumerPkg consumerPkg'
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, ledgerUnary, _regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    _endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
    _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
    endpointPkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed ledgerUnary realSealUnary ledgerRealSealConsumer
  have consumerUnary' : UnaryHistory consumer' :=
    unary_cont_closed ledgerUnary realSealUnary ledgerRealSealConsumer'
  have sameConsumer : hsame consumer consumer' :=
    cont_respects_hsame (hsame_refl ledger) (hsame_refl realSeal) ledgerRealSealConsumer
      ledgerRealSealConsumer'
  exact ⟨consumerUnary, consumerUnary', sameConsumer, endpointPkg, consumerPkg, consumerPkg'⟩

theorem CauchyCriterionCarrier_obligation_closure_package [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      consumer handoff scopedSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      CauchyCriterionNameCertCarrier window modulus ledger tolerance realSeal transport route
        provenance localCert bundle pkg ->
        Cont ledger realSeal consumer ->
          Cont regseq realSeal handoff ->
            Cont consumer provenance scopedSeal ->
              PkgSig bundle consumer pkg ->
                PkgSig bundle handoff pkg ->
                  PkgSig bundle scopedSeal pkg ->
                    SemanticNameCert
                        (fun row : BHist =>
                          CauchyCriterionNameCertCarrier window modulus ledger tolerance realSeal
                              transport route provenance localCert bundle pkg ∧ hsame row realSeal)
                        (fun row : BHist =>
                          CauchyCriterionNameCertCarrier window modulus ledger tolerance realSeal
                              transport route provenance localCert bundle pkg ∧ hsame row ledger)
                        (fun row : BHist =>
                          CauchyCriterionNameCertCarrier window modulus ledger tolerance realSeal
                              transport route provenance localCert bundle pkg ∧
                            hsame row provenance)
                        hsame ∧
                      UnaryHistory consumer ∧ UnaryHistory handoff ∧ UnaryHistory scopedSeal := by
  intro carrier nameCarrier ledgerRealSealConsumer regseqRealSealHandoff
    consumerProvenanceScopedSeal _consumerPkg _handoffPkg _scopedPkg
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, ledgerUnary, regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, provenanceUnary, _localCertUnary,
    _endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
    _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
    _endpointPkg⟩ := carrier
  have semantic :
      SemanticNameCert
        (fun row : BHist =>
          CauchyCriterionNameCertCarrier window modulus ledger tolerance realSeal transport route
              provenance localCert bundle pkg ∧ hsame row realSeal)
        (fun row : BHist =>
          CauchyCriterionNameCertCarrier window modulus ledger tolerance realSeal transport route
              provenance localCert bundle pkg ∧ hsame row ledger)
        (fun row : BHist =>
          CauchyCriterionNameCertCarrier window modulus ledger tolerance realSeal transport route
              provenance localCert bundle pkg ∧ hsame row provenance)
        hsame :=
    CauchyCriterionCarrier_namecert_obligations nameCarrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed ledgerUnary realSealUnary ledgerRealSealConsumer
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed regseqUnary realSealUnary regseqRealSealHandoff
  have scopedSealUnary : UnaryHistory scopedSeal :=
    unary_cont_closed consumerUnary provenanceUnary consumerProvenanceScopedSeal
  exact ⟨semantic, consumerUnary, handoffUnary, scopedSealUnary⟩

theorem CauchyCriterionCarrier_shared_tail_budget_seal_comparison [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      window' modulus' tolerance' ledger' regseq' realSeal' transport' route' provenance'
      localCert' endpoint' sealRead sealRead' comparison : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg →
      CauchyCriterionCarrier window' modulus' tolerance' ledger' regseq' realSeal' transport'
        route' provenance' localCert' endpoint' bundle pkg →
      hsame ledger ledger' →
      hsame realSeal realSeal' →
      Cont ledger realSeal sealRead →
      Cont ledger' realSeal' sealRead' →
      Cont sealRead sealRead' comparison →
      PkgSig bundle comparison pkg →
        hsame sealRead sealRead' ∧ UnaryHistory comparison ∧
          Cont ledger realSeal sealRead ∧ Cont ledger' realSeal' sealRead' ∧
            Cont sealRead sealRead' comparison ∧ PkgSig bundle comparison pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig
  intro carrier carrier' sameLedger sameRealSeal sealReadRow sealReadRow' comparisonRow
    comparisonPkg
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, ledgerUnary, _regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    _endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
    _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
    _endpointPkg⟩ := carrier
  obtain ⟨_windowUnary', _modulusUnary', _toleranceUnary', ledgerUnary', _regseqUnary',
    realSealUnary', _transportUnary', _routeUnary', _provenanceUnary', _localCertUnary',
    _endpointUnary', _windowModulusTolerance', _toleranceLedgerRegseq',
    _regseqRealSealTransport', _transportLocalCertRoute', _routeProvenanceEndpoint',
    _endpointPkg'⟩ := carrier'
  have sameSealRead : hsame sealRead sealRead' :=
    cont_respects_hsame sameLedger sameRealSeal sealReadRow sealReadRow'
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed ledgerUnary realSealUnary sealReadRow
  have sealReadUnary' : UnaryHistory sealRead' :=
    unary_cont_closed ledgerUnary' realSealUnary' sealReadRow'
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed sealReadUnary sealReadUnary' comparisonRow
  exact
    ⟨sameSealRead, comparisonUnary, sealReadRow, sealReadRow', comparisonRow, comparisonPkg⟩

end BEDC.Derived.CauchyCriterionUp
