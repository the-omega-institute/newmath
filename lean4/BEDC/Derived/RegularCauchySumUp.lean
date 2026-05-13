import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History
import BEDC.Derived.RegularCauchyLimitClassifierUp

namespace BEDC.Derived.RegularCauchySumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchySumCarrier [AskSetup] [PackageSetup]
    (leftSource rightSource leftWindow rightWindow leftEndpoint rightEndpoint sumEndpoint budget
      readback transports routes provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory leftSource ∧ UnaryHistory rightSource ∧ UnaryHistory leftWindow ∧
    UnaryHistory rightWindow ∧ UnaryHistory leftEndpoint ∧ UnaryHistory rightEndpoint ∧
      UnaryHistory budget ∧ UnaryHistory transports ∧ UnaryHistory routes ∧
        UnaryHistory provenance ∧ UnaryHistory localCert ∧ Cont leftWindow leftEndpoint transports ∧
          Cont rightWindow rightEndpoint routes ∧ Cont leftEndpoint rightEndpoint sumEndpoint ∧
            Cont sumEndpoint budget readback ∧ Cont readback routes provenance ∧
              PkgSig bundle provenance pkg

theorem RegularCauchySumCarrier_window_budget [AskSetup] [PackageSetup]
    {leftSource rightSource leftWindow rightWindow leftEndpoint rightEndpoint sumEndpoint budget
      readback transports routes provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySumCarrier leftSource rightSource leftWindow rightWindow leftEndpoint
        rightEndpoint sumEndpoint budget readback transports routes provenance localCert bundle pkg ->
      UnaryHistory sumEndpoint ∧ UnaryHistory readback ∧ Cont leftEndpoint rightEndpoint
        sumEndpoint ∧ Cont sumEndpoint budget readback ∧ PkgSig bundle provenance pkg := by
  intro carrier
  cases carrier with
  | intro leftSourceUnary carrier =>
      cases carrier with
      | intro rightSourceUnary carrier =>
          cases carrier with
          | intro leftWindowUnary carrier =>
              cases carrier with
              | intro rightWindowUnary carrier =>
                  cases carrier with
                  | intro leftEndpointUnary carrier =>
                      cases carrier with
                      | intro rightEndpointUnary carrier =>
                          cases carrier with
                          | intro budgetUnary carrier =>
                              cases carrier with
                              | intro transportsUnary carrier =>
                                  cases carrier with
                                  | intro routesUnary carrier =>
                                      cases carrier with
                                      | intro provenanceUnary carrier =>
                                          cases carrier with
                                          | intro localCertUnary carrier =>
                                              cases carrier with
                                              | intro leftRoute carrier =>
                                                  cases carrier with
                                                  | intro rightRoute carrier =>
                                                      cases carrier with
                                                      | intro sumEndpointRoute carrier =>
                                                          cases carrier with
                                                          | intro readbackRoute carrier =>
                                                              cases carrier with
                                                              | intro provenanceRoute pkgSig =>
                                                                  have sumEndpointUnary :
                                                                      UnaryHistory sumEndpoint :=
                                                                    unary_cont_closed
                                                                      leftEndpointUnary
                                                                      rightEndpointUnary
                                                                      sumEndpointRoute
                                                                  have readbackUnary :
                                                                      UnaryHistory readback :=
                                                                    unary_cont_closed
                                                                      sumEndpointUnary
                                                                      budgetUnary
                                                                      readbackRoute
                                                                  exact
                                                                    ⟨sumEndpointUnary,
                                                                      readbackUnary,
                                                                      sumEndpointRoute,
                                                                      readbackRoute,
                                                                      pkgSig⟩

theorem RegularCauchySumCarrier_regseqrat_handoff [AskSetup] [PackageSetup]
    {leftSource rightSource leftWindow rightWindow leftEndpoint rightEndpoint sumEndpoint budget
      readback transports routes provenance localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySumCarrier leftSource rightSource leftWindow rightWindow leftEndpoint
        rightEndpoint sumEndpoint budget readback transports routes provenance localCert bundle pkg ->
      Cont readback routes consumer ->
        UnaryHistory readback ∧ UnaryHistory consumer ∧ Cont sumEndpoint budget readback ∧
          Cont readback routes provenance ∧ hsame consumer (append readback routes) ∧
            PkgSig bundle provenance pkg := by
  intro carrier consumerRoute
  cases carrier with
  | intro leftSourceUnary carrier =>
      cases carrier with
      | intro rightSourceUnary carrier =>
          cases carrier with
          | intro leftWindowUnary carrier =>
              cases carrier with
              | intro rightWindowUnary carrier =>
                  cases carrier with
                  | intro leftEndpointUnary carrier =>
                      cases carrier with
                      | intro rightEndpointUnary carrier =>
                          cases carrier with
                          | intro budgetUnary carrier =>
                              cases carrier with
                              | intro transportsUnary carrier =>
                                  cases carrier with
                                  | intro routesUnary carrier =>
                                      cases carrier with
                                      | intro provenanceUnary carrier =>
                                          cases carrier with
                                          | intro localCertUnary carrier =>
                                              cases carrier with
                                              | intro leftRoute carrier =>
                                                  cases carrier with
                                                  | intro rightRoute carrier =>
                                                      cases carrier with
                                                      | intro sumEndpointRoute carrier =>
                                                          cases carrier with
                                                          | intro readbackRoute carrier =>
                                                              cases carrier with
                                                              | intro provenanceRoute pkgSig =>
                                                                  have sumEndpointUnary :
                                                                      UnaryHistory sumEndpoint :=
                                                                    unary_cont_closed
                                                                      leftEndpointUnary
                                                                      rightEndpointUnary
                                                                      sumEndpointRoute
                                                                  have readbackUnary :
                                                                      UnaryHistory readback :=
                                                                    unary_cont_closed
                                                                      sumEndpointUnary
                                                                      budgetUnary
                                                                      readbackRoute
                                                                  have consumerUnary :
                                                                      UnaryHistory consumer :=
                                                                    unary_cont_closed
                                                                      readbackUnary routesUnary
                                                                      consumerRoute
                                                                  exact
                                                                    ⟨readbackUnary,
                                                                      consumerUnary,
                                                                      readbackRoute,
                                                                      provenanceRoute,
                                                                      consumerRoute,
                                                                      pkgSig⟩

theorem RegularCauchySumCarrier_symmetric_input_handoff [AskSetup] [PackageSetup]
    {leftSource rightSource leftWindow rightWindow leftEndpoint rightEndpoint sumEndpoint budget
      readback transports routes provenance localCert swappedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySumCarrier leftSource rightSource leftWindow rightWindow leftEndpoint
        rightEndpoint sumEndpoint budget readback transports routes provenance localCert bundle pkg ->
      Cont rightEndpoint leftEndpoint swappedEndpoint ->
        UnaryHistory swappedEndpoint ∧ hsame sumEndpoint swappedEndpoint ∧
          Cont leftEndpoint rightEndpoint sumEndpoint ∧
            Cont rightEndpoint leftEndpoint swappedEndpoint ∧ PkgSig bundle provenance pkg := by
  intro carrier swappedRoute
  obtain ⟨_leftSourceUnary, _rightSourceUnary, _leftWindowUnary, _rightWindowUnary,
    leftEndpointUnary, rightEndpointUnary, _budgetUnary, _transportsUnary, _routesUnary,
    _provenanceUnary, _localCertUnary, _leftRoute, _rightRoute, sumEndpointRoute,
    _readbackRoute, _provenanceRoute, pkgSig⟩ := carrier
  have swappedUnary : UnaryHistory swappedEndpoint :=
    unary_cont_closed rightEndpointUnary leftEndpointUnary swappedRoute
  have sameSumSwapped : hsame sumEndpoint swappedEndpoint :=
    unary_cont_comm leftEndpointUnary rightEndpointUnary sumEndpointRoute swappedRoute
  exact ⟨swappedUnary, sameSumSwapped, sumEndpointRoute, swappedRoute, pkgSig⟩

theorem RegularCauchySumCarrier_realup_seal_nonempty_iff [AskSetup] [PackageSetup]
    {leftSource rightSource leftWindow rightWindow leftEndpoint rightEndpoint sumEndpoint budget
      readback transports routes provenance localCert realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySumCarrier leftSource rightSource leftWindow rightWindow leftEndpoint
        rightEndpoint sumEndpoint budget readback transports routes provenance localCert bundle pkg ->
      Cont readback provenance realSeal ->
        UnaryHistory realSeal ∧
          (((hsame realSeal BHist.Empty -> False) ↔
              (hsame readback BHist.Empty -> False) ∨
                (hsame provenance BHist.Empty -> False))) ∧
            PkgSig bundle provenance pkg := by
  intro carrier realSealRow
  obtain ⟨_leftSourceUnary, _rightSourceUnary, _leftWindowUnary, _rightWindowUnary,
    leftEndpointUnary, rightEndpointUnary, budgetUnary, _transportsUnary, routesUnary,
    provenanceUnary, _localCertUnary, _leftRoute, _rightRoute, sumEndpointRoute,
    readbackRoute, _provenanceRoute, pkgSig⟩ := carrier
  have sumEndpointUnary : UnaryHistory sumEndpoint :=
    unary_cont_closed leftEndpointUnary rightEndpointUnary sumEndpointRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed sumEndpointUnary budgetUnary readbackRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed readbackUnary provenanceUnary realSealRow
  have realSealNonempty :
      ((hsame realSeal BHist.Empty -> False) ↔
        (hsame readback BHist.Empty -> False) ∨
          (hsame provenance BHist.Empty -> False)) := by
    cases realSealRow
    exact append_nonempty_iff
  exact ⟨realSealUnary, realSealNonempty, pkgSig⟩

theorem RegularCauchySumCarrier_seal_consumer_exhaustion [AskSetup] [PackageSetup]
    {leftSource rightSource leftWindow rightWindow leftEndpoint rightEndpoint sumEndpoint budget
      readback transports routes provenance localCert realSeal consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySumCarrier leftSource rightSource leftWindow rightWindow leftEndpoint
        rightEndpoint sumEndpoint budget readback transports routes provenance localCert bundle pkg ->
      Cont readback provenance realSeal ->
        Cont realSeal localCert consumer ->
          PkgSig bundle consumer pkg ->
            UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory consumer ∧
              Cont sumEndpoint budget readback ∧ Cont readback provenance realSeal ∧
                Cont realSeal localCert consumer ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle consumer pkg := by
  intro carrier realSealRow consumerRow consumerPkg
  obtain ⟨_leftSourceUnary, _rightSourceUnary, _leftWindowUnary, _rightWindowUnary,
    leftEndpointUnary, rightEndpointUnary, budgetUnary, _transportsUnary, _routesUnary,
    provenanceUnary, localCertUnary, _leftRoute, _rightRoute, sumEndpointRoute,
    readbackRoute, _provenanceRoute, pkgSig⟩ := carrier
  have sumEndpointUnary : UnaryHistory sumEndpoint :=
    unary_cont_closed leftEndpointUnary rightEndpointUnary sumEndpointRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed sumEndpointUnary budgetUnary readbackRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed readbackUnary provenanceUnary realSealRow
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed realSealUnary localCertUnary consumerRow
  exact
    ⟨readbackUnary, realSealUnary, consumerUnary, readbackRoute, realSealRow, consumerRow,
      pkgSig, consumerPkg⟩

theorem RegularCauchySumCarrier_consumer_obligation_package [AskSetup] [PackageSetup]
    {leftSource rightSource leftWindow rightWindow leftEndpoint rightEndpoint sumEndpoint budget
      readback transports routes provenance localCert realSeal consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySumCarrier leftSource rightSource leftWindow rightWindow leftEndpoint
        rightEndpoint sumEndpoint budget readback transports routes provenance localCert bundle pkg →
      Cont readback provenance realSeal →
        Cont realSeal localCert consumer →
          PkgSig bundle consumer pkg →
            UnaryHistory leftSource ∧ UnaryHistory rightSource ∧ UnaryHistory sumEndpoint ∧
              UnaryHistory budget ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
                UnaryHistory consumer ∧ Cont leftEndpoint rightEndpoint sumEndpoint ∧
                  Cont sumEndpoint budget readback ∧ Cont readback provenance realSeal ∧
                    Cont realSeal localCert consumer ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier realSealRow consumerRow consumerPkg
  obtain ⟨leftSourceUnary, rightSourceUnary, _leftWindowUnary, _rightWindowUnary,
    leftEndpointUnary, rightEndpointUnary, budgetUnary, _transportsUnary, _routesUnary,
    provenanceUnary, localCertUnary, _leftRoute, _rightRoute, sumEndpointRoute,
    readbackRoute, _provenanceRoute, pkgSig⟩ := carrier
  have sumEndpointUnary : UnaryHistory sumEndpoint :=
    unary_cont_closed leftEndpointUnary rightEndpointUnary sumEndpointRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed sumEndpointUnary budgetUnary readbackRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed readbackUnary provenanceUnary realSealRow
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed realSealUnary localCertUnary consumerRow
  exact
    ⟨leftSourceUnary,
      rightSourceUnary,
      sumEndpointUnary,
      budgetUnary,
      readbackUnary,
      realSealUnary,
      consumerUnary,
      sumEndpointRoute,
      readbackRoute,
      realSealRow,
      consumerRow,
      pkgSig,
      consumerPkg⟩

theorem RegularCauchySumCarrier_limit_classifier_compatibility [AskSetup] [PackageSetup]
    {leftSource rightSource leftWindow rightWindow leftEndpoint rightEndpoint sumEndpoint budget
      readback sumTransports sumRoutes sumProvenance localCert : BHist}
    {input modulus diagonal windows ledger sealRow transportRow limitRoutes limitProvenance cert
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySumCarrier leftSource rightSource leftWindow rightWindow leftEndpoint
        rightEndpoint sumEndpoint budget readback sumTransports sumRoutes sumProvenance localCert
        bundle pkg →
      BEDC.Derived.RegularCauchyLimitClassifierUp.RegularCauchyLimitClassifierCarrier input
        modulus diagonal windows readback ledger sealRow transportRow limitRoutes limitProvenance
        cert bundle pkg →
        Cont cert limitRoutes publicRead →
          PkgSig bundle publicRead pkg →
            UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory cert ∧
              UnaryHistory publicRead ∧ Cont sumEndpoint budget readback ∧
                Cont diagonal windows readback ∧ Cont readback ledger sealRow ∧
                  hsame cert (append limitProvenance sealRow) ∧
                    PkgSig bundle sumProvenance pkg ∧ PkgSig bundle cert pkg ∧
                      PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro sumCarrier limitCarrier certRoutesPublicRead publicReadPkg
  obtain ⟨_leftSourceUnary, _rightSourceUnary, _leftWindowUnary, _rightWindowUnary,
    leftEndpointUnary, rightEndpointUnary, budgetUnary, _sumTransportsUnary, _sumRoutesUnary,
    _sumProvenanceUnary, _localCertUnary, _leftRoute, _rightRoute, sumEndpointRoute,
    readbackRoute, _sumProvenanceRoute, sumProvenancePkg⟩ := sumCarrier
  have sumEndpointUnary : UnaryHistory sumEndpoint :=
    unary_cont_closed leftEndpointUnary rightEndpointUnary sumEndpointRoute
  have readbackUnaryFromSum : UnaryHistory readback :=
    unary_cont_closed sumEndpointUnary budgetUnary readbackRoute
  have boundary :=
    _root_.BEDC.Derived.RegularCauchyLimitClassifierUp.RegularCauchyLimitClassifierCarrier_diagonal_window_public_boundary
      limitCarrier certRoutesPublicRead publicReadPkg
  obtain ⟨_readbackUnaryFromLimit, _ledgerUnary, sealRowUnary, certUnary, publicReadUnary,
    diagonalWindowsReadback, readbackLedgerSeal, _certRoutesPublicRead, sameCert,
    certPkg, publicReadPkg'⟩ := boundary
  exact
    ⟨readbackUnaryFromSum,
      sealRowUnary,
      certUnary,
      publicReadUnary,
      readbackRoute,
      diagonalWindowsReadback,
      readbackLedgerSeal,
      sameCert,
      sumProvenancePkg,
      certPkg,
      publicReadPkg'⟩

end BEDC.Derived.RegularCauchySumUp
