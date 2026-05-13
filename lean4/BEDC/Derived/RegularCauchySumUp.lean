import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

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

theorem RegularCauchySumCarrier_classifier_stability [AskSetup] [PackageSetup]
    {leftSource rightSource leftWindow rightWindow leftEndpoint rightEndpoint sumEndpoint budget
      readback transports routes provenance localCert leftSource' rightSource' leftWindow'
      rightWindow' leftEndpoint' rightEndpoint' sumEndpoint' budget' readback' transports'
      routes' provenance' localCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySumCarrier leftSource rightSource leftWindow rightWindow leftEndpoint
        rightEndpoint sumEndpoint budget readback transports routes provenance localCert bundle pkg →
      hsame leftSource leftSource' →
        hsame rightSource rightSource' →
          hsame leftWindow leftWindow' →
            hsame rightWindow rightWindow' →
              hsame leftEndpoint leftEndpoint' →
                hsame rightEndpoint rightEndpoint' →
                  hsame sumEndpoint sumEndpoint' →
                    hsame budget budget' →
                      hsame readback readback' →
                        hsame transports transports' →
                          hsame routes routes' →
                            hsame provenance provenance' →
                              hsame localCert localCert' →
                                Cont leftWindow' leftEndpoint' transports' →
                                  Cont rightWindow' rightEndpoint' routes' →
                                    Cont leftEndpoint' rightEndpoint' sumEndpoint' →
                                      Cont sumEndpoint' budget' readback' →
                                        Cont readback' routes' provenance' →
                                          PkgSig bundle provenance' pkg →
                                            RegularCauchySumCarrier leftSource'
                                                rightSource' leftWindow' rightWindow'
                                                leftEndpoint' rightEndpoint' sumEndpoint' budget'
                                                readback' transports' routes' provenance'
                                                localCert' bundle pkg ∧
                                              hsame provenance provenance' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier sameLeftSource sameRightSource sameLeftWindow sameRightWindow
    sameLeftEndpoint sameRightEndpoint _sameSumEndpoint sameBudget _sameReadback
    sameTransports sameRoutes sameProvenance sameLocalCert leftRoute rightRoute sumRoute
    readbackRoute provenanceRoute provenancePkg
  obtain ⟨leftSourceUnary, rightSourceUnary, leftWindowUnary, rightWindowUnary,
    leftEndpointUnary, rightEndpointUnary, budgetUnary, transportsUnary, routesUnary,
    provenanceUnary, localCertUnary, _oldLeftRoute, _oldRightRoute, _oldSumRoute,
    _oldReadbackRoute, _oldProvenanceRoute, _oldPkgSig⟩ := carrier
  have leftSourceUnary' : UnaryHistory leftSource' :=
    unary_transport leftSourceUnary sameLeftSource
  have rightSourceUnary' : UnaryHistory rightSource' :=
    unary_transport rightSourceUnary sameRightSource
  have leftWindowUnary' : UnaryHistory leftWindow' :=
    unary_transport leftWindowUnary sameLeftWindow
  have rightWindowUnary' : UnaryHistory rightWindow' :=
    unary_transport rightWindowUnary sameRightWindow
  have leftEndpointUnary' : UnaryHistory leftEndpoint' :=
    unary_transport leftEndpointUnary sameLeftEndpoint
  have rightEndpointUnary' : UnaryHistory rightEndpoint' :=
    unary_transport rightEndpointUnary sameRightEndpoint
  have budgetUnary' : UnaryHistory budget' :=
    unary_transport budgetUnary sameBudget
  have transportsUnary' : UnaryHistory transports' :=
    unary_transport transportsUnary sameTransports
  have routesUnary' : UnaryHistory routes' :=
    unary_transport routesUnary sameRoutes
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have localCertUnary' : UnaryHistory localCert' :=
    unary_transport localCertUnary sameLocalCert
  exact
    ⟨⟨leftSourceUnary',
      rightSourceUnary',
      leftWindowUnary',
      rightWindowUnary',
      leftEndpointUnary',
      rightEndpointUnary',
      budgetUnary',
      transportsUnary',
      routesUnary',
      provenanceUnary',
      localCertUnary',
      leftRoute,
      rightRoute,
      sumRoute,
      readbackRoute,
      provenanceRoute,
      provenancePkg⟩,
      sameProvenance⟩

end BEDC.Derived.RegularCauchySumUp
