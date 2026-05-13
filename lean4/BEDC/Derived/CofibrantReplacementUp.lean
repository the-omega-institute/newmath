import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CofibrantReplacementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CofibrantReplacementBHistSource [AskSetup] [PackageSetup]
    (object cofibrant arrow factorization lifting dependency ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory object ∧ UnaryHistory cofibrant ∧ UnaryHistory factorization ∧
    UnaryHistory lifting ∧ UnaryHistory dependency ∧ Cont object cofibrant arrow ∧
      Cont arrow factorization ledger ∧ Cont ledger dependency endpoint ∧
        PkgSig bundle endpoint pkg

theorem CofibrantReplacementBHistSource_factorization_transport [AskSetup] [PackageSetup]
    {object cofibrant arrow factorization lifting pkgrow ledger object' cofibrant' arrow'
      factorization' lifting' pkgrow' ledger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofibrantReplacementBHistSource object cofibrant arrow factorization lifting pkgrow ledger
        (append ledger pkgrow) bundle pkg ->
      hsame object object' ->
        hsame cofibrant cofibrant' ->
          hsame factorization factorization' ->
            hsame pkgrow pkgrow' ->
              UnaryHistory lifting' ->
                Cont object' cofibrant' arrow' ->
                  Cont arrow' factorization' ledger' ->
                    Cont ledger' pkgrow' endpoint' ->
                      PkgSig bundle endpoint' pkg ->
                        CofibrantReplacementBHistSource object' cofibrant' arrow' factorization'
                            lifting' pkgrow' ledger' endpoint' bundle pkg ∧
                          hsame arrow arrow' ∧ hsame ledger ledger' ∧
                            hsame (append ledger pkgrow) endpoint' := by
  intro source sameObject sameCofibrant sameFactorization samePkgrow
  intro liftingUnary' targetObject targetFactorization targetPkg targetPkgSig
  have objectUnary' : UnaryHistory object' :=
    unary_transport source.left sameObject
  have cofibrantUnary' : UnaryHistory cofibrant' :=
    unary_transport source.right.left sameCofibrant
  have factorizationUnary' : UnaryHistory factorization' :=
    unary_transport source.right.right.left sameFactorization
  have pkgrowUnary' : UnaryHistory pkgrow' :=
    unary_transport source.right.right.right.right.left samePkgrow
  have sameArrow : hsame arrow arrow' :=
    cont_respects_hsame sameObject sameCofibrant
      source.right.right.right.right.right.left targetObject
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameArrow sameFactorization
      source.right.right.right.right.right.right.left targetFactorization
  have sameEndpoint : hsame (append ledger pkgrow) endpoint' :=
    cont_respects_hsame sameLedger samePkgrow
      source.right.right.right.right.right.right.right.left targetPkg
  exact
    And.intro
      (And.intro objectUnary'
        (And.intro cofibrantUnary'
          (And.intro factorizationUnary'
            (And.intro liftingUnary'
              (And.intro pkgrowUnary'
                (And.intro targetObject
                  (And.intro targetFactorization (And.intro targetPkg targetPkgSig))))))))
      (And.intro sameArrow (And.intro sameLedger sameEndpoint))

theorem CofibrantReplacementBHistSource_factorization_obligation [AskSetup] [PackageSetup]
    {object cofibrant arrow factorization lifting dependency ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofibrantReplacementBHistSource object cofibrant arrow factorization lifting dependency
        ledger endpoint bundle pkg ->
      UnaryHistory object ∧ UnaryHistory cofibrant ∧ UnaryHistory arrow ∧
        UnaryHistory factorization ∧ UnaryHistory lifting ∧ UnaryHistory dependency ∧
          UnaryHistory endpoint ∧ Cont object cofibrant arrow ∧
            Cont arrow factorization ledger ∧ Cont ledger dependency endpoint ∧
              PkgSig bundle endpoint pkg := by
  intro source
  have objectUnary : UnaryHistory object :=
    source.left
  have cofibrantUnary : UnaryHistory cofibrant :=
    source.right.left
  have factorizationUnary : UnaryHistory factorization :=
    source.right.right.left
  have liftingUnary : UnaryHistory lifting :=
    source.right.right.right.left
  have dependencyUnary : UnaryHistory dependency :=
    source.right.right.right.right.left
  have arrowRow : Cont object cofibrant arrow :=
    source.right.right.right.right.right.left
  have ledgerRow : Cont arrow factorization ledger :=
    source.right.right.right.right.right.right.left
  have endpointRow : Cont ledger dependency endpoint :=
    source.right.right.right.right.right.right.right.left
  have packageBoundary : PkgSig bundle endpoint pkg :=
    source.right.right.right.right.right.right.right.right
  have arrowUnary : UnaryHistory arrow :=
    unary_cont_closed objectUnary cofibrantUnary arrowRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed arrowUnary factorizationUnary ledgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledgerUnary dependencyUnary endpointRow
  exact And.intro objectUnary
    (And.intro cofibrantUnary
      (And.intro arrowUnary
        (And.intro factorizationUnary
          (And.intro liftingUnary
            (And.intro dependencyUnary
              (And.intro endpointUnary
                (And.intro arrowRow
                  (And.intro ledgerRow (And.intro endpointRow packageBoundary)))))))))

theorem CofibrantReplacementBHistSource_factorization_readback [AskSetup] [PackageSetup]
    {object cofibrant arrow factorization lifting dependency ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofibrantReplacementBHistSource object cofibrant arrow factorization lifting dependency
        ledger endpoint bundle pkg ->
      UnaryHistory arrow ∧ UnaryHistory ledger ∧ hsame ledger (append arrow factorization) ∧
        UnaryHistory endpoint ∧ hsame endpoint (append ledger dependency) ∧
          PkgSig bundle endpoint pkg := by
  intro source
  have objectUnary : UnaryHistory object :=
    source.left
  have cofibrantUnary : UnaryHistory cofibrant :=
    source.right.left
  have factorizationUnary : UnaryHistory factorization :=
    source.right.right.left
  have dependencyUnary : UnaryHistory dependency :=
    source.right.right.right.right.left
  have arrowRow : Cont object cofibrant arrow :=
    source.right.right.right.right.right.left
  have ledgerRow : Cont arrow factorization ledger :=
    source.right.right.right.right.right.right.left
  have endpointRow : Cont ledger dependency endpoint :=
    source.right.right.right.right.right.right.right.left
  have packageBoundary : PkgSig bundle endpoint pkg :=
    source.right.right.right.right.right.right.right.right
  have arrowUnary : UnaryHistory arrow :=
    unary_cont_closed objectUnary cofibrantUnary arrowRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed arrowUnary factorizationUnary ledgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledgerUnary dependencyUnary endpointRow
  exact And.intro arrowUnary
    (And.intro ledgerUnary
      (And.intro ledgerRow
        (And.intro endpointUnary
          (And.intro endpointRow packageBoundary))))

theorem CofibrantReplacementBHistSource_namecert_obligation_surface [AskSetup] [PackageSetup]
    {object cofibrant arrow factorization lifting dependency ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofibrantReplacementBHistSource object cofibrant arrow factorization lifting dependency
        ledger endpoint bundle pkg ->
      UnaryHistory object ∧ UnaryHistory cofibrant ∧ UnaryHistory arrow ∧
        UnaryHistory factorization ∧ UnaryHistory lifting ∧ UnaryHistory dependency ∧
          UnaryHistory ledger ∧ UnaryHistory endpoint ∧ Cont object cofibrant arrow ∧
            Cont arrow factorization ledger ∧ Cont ledger dependency endpoint ∧
              PkgSig bundle endpoint pkg := by
  intro source
  obtain ⟨objectUnary, cofibrantUnary, factorizationUnary, liftingUnary, dependencyUnary,
    arrowRow, ledgerRow, endpointRow, endpointPkg⟩ := source
  have arrowUnary : UnaryHistory arrow :=
    unary_cont_closed objectUnary cofibrantUnary arrowRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed arrowUnary factorizationUnary ledgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledgerUnary dependencyUnary endpointRow
  exact
    And.intro objectUnary
      (And.intro cofibrantUnary
        (And.intro arrowUnary
          (And.intro factorizationUnary
            (And.intro liftingUnary
              (And.intro dependencyUnary
                (And.intro ledgerUnary
                  (And.intro endpointUnary
                    (And.intro arrowRow
                      (And.intro ledgerRow
                        (And.intro endpointRow endpointPkg))))))))))

theorem CofibrantReplacementNameCertObligationSurface_dependency_transport [AskSetup]
    [PackageSetup]
    {object cofibrant arrow factorization lifting dependency ledger endpoint dependency'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofibrantReplacementBHistSource object cofibrant arrow factorization lifting dependency
        ledger endpoint bundle pkg ->
      hsame dependency dependency' -> Cont ledger dependency' endpoint' ->
        PkgSig bundle endpoint' pkg ->
          CofibrantReplacementBHistSource object cofibrant arrow factorization lifting
              dependency' ledger endpoint' bundle pkg ∧
            UnaryHistory object ∧ UnaryHistory cofibrant ∧ UnaryHistory arrow ∧
              UnaryHistory factorization ∧ UnaryHistory lifting ∧ UnaryHistory dependency' ∧
                UnaryHistory endpoint' ∧ Cont object cofibrant arrow ∧
                  Cont arrow factorization ledger ∧ Cont ledger dependency' endpoint' ∧
                    hsame endpoint endpoint' ∧ PkgSig bundle endpoint' pkg := by
  intro source sameDependency endpointRow' endpointSig'
  have objectUnary : UnaryHistory object :=
    source.left
  have cofibrantUnary : UnaryHistory cofibrant :=
    source.right.left
  have factorizationUnary : UnaryHistory factorization :=
    source.right.right.left
  have liftingUnary : UnaryHistory lifting :=
    source.right.right.right.left
  have dependencyUnary : UnaryHistory dependency :=
    source.right.right.right.right.left
  have arrowRow : Cont object cofibrant arrow :=
    source.right.right.right.right.right.left
  have ledgerRow : Cont arrow factorization ledger :=
    source.right.right.right.right.right.right.left
  have endpointRow : Cont ledger dependency endpoint :=
    source.right.right.right.right.right.right.right.left
  have dependencyUnary' : UnaryHistory dependency' :=
    unary_transport dependencyUnary sameDependency
  have arrowUnary : UnaryHistory arrow :=
    unary_cont_closed objectUnary cofibrantUnary arrowRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed arrowUnary factorizationUnary ledgerRow
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed ledgerUnary dependencyUnary' endpointRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame (hsame_refl ledger) sameDependency endpointRow endpointRow'
  exact
    ⟨⟨objectUnary, cofibrantUnary, factorizationUnary, liftingUnary, dependencyUnary',
        arrowRow, ledgerRow, endpointRow', endpointSig'⟩,
      objectUnary,
      cofibrantUnary,
      arrowUnary,
      factorizationUnary,
      liftingUnary,
      dependencyUnary',
      endpointUnary',
      arrowRow,
      ledgerRow,
      endpointRow',
      sameEndpoint,
      endpointSig'⟩

def CofibrantReplacementPacket [AskSetup] [PackageSetup]
    (X Q arrow factorization lifting package ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory X ∧ UnaryHistory Q ∧ UnaryHistory arrow ∧ UnaryHistory factorization ∧
    UnaryHistory lifting ∧ UnaryHistory package ∧ Cont arrow factorization ledger ∧
      Cont ledger package endpoint ∧ PkgSig bundle endpoint pkg

theorem CofibrantReplacementPacket_weak_equivalence_ledger_transport [AskSetup]
    [PackageSetup]
    {X Q arrow factorization lifting package ledger endpoint X' Q' arrow' factorization'
      lifting' package' ledger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofibrantReplacementPacket X Q arrow factorization lifting package ledger endpoint
        bundle pkg ->
      hsame X X' -> hsame Q Q' -> hsame arrow arrow' ->
        hsame factorization factorization' -> hsame lifting lifting' ->
          hsame package package' -> Cont arrow' factorization' ledger' ->
            Cont ledger' package' endpoint' -> PkgSig bundle endpoint' pkg ->
              CofibrantReplacementPacket X' Q' arrow' factorization' lifting' package'
                  ledger' endpoint' bundle pkg ∧
                hsame ledger ledger' ∧ hsame endpoint endpoint' := by
  intro packet sameX sameQ sameArrow sameFactorization sameLifting samePackage
  intro ledgerRow' endpointRow' pkgSig'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameArrow sameFactorization
      packet.right.right.right.right.right.right.left ledgerRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameLedger samePackage
      packet.right.right.right.right.right.right.right.left endpointRow'
  have transported :
      CofibrantReplacementPacket X' Q' arrow' factorization' lifting' package' ledger'
          endpoint' bundle pkg :=
    ⟨unary_transport packet.left sameX,
      unary_transport packet.right.left sameQ,
      unary_transport packet.right.right.left sameArrow,
      unary_transport packet.right.right.right.left sameFactorization,
      unary_transport packet.right.right.right.right.left sameLifting,
      unary_transport packet.right.right.right.right.right.left samePackage,
      ledgerRow',
      endpointRow',
      pkgSig'⟩
  exact ⟨transported, sameLedger, sameEndpoint⟩

theorem CofibrantReplacementPacket_dependency_boundary [AskSetup] [PackageSetup]
    {X Q arrow factorization lifting package ledger endpoint dependencyRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofibrantReplacementPacket X Q arrow factorization lifting package ledger endpoint
        bundle pkg ->
      Cont endpoint package dependencyRow ->
        PkgSig bundle dependencyRow pkg ->
          UnaryHistory X ∧ UnaryHistory Q ∧ UnaryHistory arrow ∧
            UnaryHistory factorization ∧ UnaryHistory lifting ∧ UnaryHistory package ∧
              UnaryHistory ledger ∧ UnaryHistory endpoint ∧ UnaryHistory dependencyRow ∧
                Cont arrow factorization ledger ∧ Cont ledger package endpoint ∧
                  Cont endpoint package dependencyRow ∧ hsame ledger (append arrow factorization) ∧
                    hsame endpoint (append ledger package) ∧
                      hsame dependencyRow (append endpoint package) ∧
                        PkgSig bundle dependencyRow pkg := by
  intro packet dependencyRowCont dependencyRowSig
  obtain ⟨XUnary, QUnary, arrowUnary, factorizationUnary, liftingUnary, packageUnary,
    ledgerRow, endpointRow, _endpointSig⟩ := packet
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed arrowUnary factorizationUnary ledgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledgerUnary packageUnary endpointRow
  have dependencyRowUnary : UnaryHistory dependencyRow :=
    unary_cont_closed endpointUnary packageUnary dependencyRowCont
  exact
    ⟨XUnary, QUnary, arrowUnary, factorizationUnary, liftingUnary, packageUnary, ledgerUnary,
      endpointUnary, dependencyRowUnary, ledgerRow, endpointRow, dependencyRowCont, ledgerRow,
      endpointRow, dependencyRowCont, dependencyRowSig⟩

theorem CofibrantReplacementBHistSource_dependency_boundary [AskSetup] [PackageSetup]
    {object cofibrant arrow factorization lifting dependency ledger endpoint consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofibrantReplacementBHistSource object cofibrant arrow factorization lifting dependency
        ledger endpoint bundle pkg ->
      Cont endpoint dependency consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory dependency ∧ UnaryHistory ledger ∧ UnaryHistory endpoint ∧
            UnaryHistory consumer ∧ Cont ledger dependency endpoint ∧
              Cont endpoint dependency consumer ∧ PkgSig bundle consumer pkg := by
  intro source consumerRow consumerSig
  obtain ⟨objectUnary, cofibrantUnary, factorizationUnary, _liftingUnary, dependencyUnary,
    objectCofibrantArrow, arrowFactorizationLedger, ledgerDependencyEndpoint,
    _endpointSig⟩ := source
  have arrowUnary : UnaryHistory arrow :=
    unary_cont_closed objectUnary cofibrantUnary objectCofibrantArrow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed arrowUnary factorizationUnary arrowFactorizationLedger
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledgerUnary dependencyUnary ledgerDependencyEndpoint
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed endpointUnary dependencyUnary consumerRow
  exact
    ⟨dependencyUnary, ledgerUnary, endpointUnary, consumerUnary, ledgerDependencyEndpoint,
      consumerRow, consumerSig⟩

theorem CofibrantReplacementBHistSource_scoped_kernel_dependency_package [AskSetup]
    [PackageSetup]
    {object cofibrant arrow factorization lifting dependency ledger endpoint scopedRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofibrantReplacementBHistSource object cofibrant arrow factorization lifting dependency
        ledger endpoint bundle pkg ->
      Cont endpoint dependency scopedRow ->
        PkgSig bundle scopedRow pkg ->
          UnaryHistory object ∧ UnaryHistory cofibrant ∧ UnaryHistory arrow ∧
            UnaryHistory factorization ∧ UnaryHistory lifting ∧ UnaryHistory dependency ∧
              UnaryHistory ledger ∧ UnaryHistory endpoint ∧ UnaryHistory scopedRow ∧
                Cont object cofibrant arrow ∧ Cont arrow factorization ledger ∧
                  Cont ledger dependency endpoint ∧ Cont endpoint dependency scopedRow ∧
                    hsame scopedRow (append endpoint dependency) ∧
                      PkgSig bundle scopedRow pkg := by
  intro source scopedRowCont scopedRowSig
  obtain ⟨objectUnary, cofibrantUnary, factorizationUnary, liftingUnary, dependencyUnary,
    objectCofibrantArrow, arrowFactorizationLedger, ledgerDependencyEndpoint,
    _endpointSig⟩ := source
  have arrowUnary : UnaryHistory arrow :=
    unary_cont_closed objectUnary cofibrantUnary objectCofibrantArrow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed arrowUnary factorizationUnary arrowFactorizationLedger
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledgerUnary dependencyUnary ledgerDependencyEndpoint
  have scopedRowUnary : UnaryHistory scopedRow :=
    unary_cont_closed endpointUnary dependencyUnary scopedRowCont
  exact
    ⟨objectUnary, cofibrantUnary, arrowUnary, factorizationUnary, liftingUnary, dependencyUnary,
      ledgerUnary, endpointUnary, scopedRowUnary, objectCofibrantArrow, arrowFactorizationLedger,
      ledgerDependencyEndpoint, scopedRowCont, scopedRowCont, scopedRowSig⟩

theorem CofibrantReplacementPacket_five_row_namecert_surface [AskSetup] [PackageSetup]
    {X Q arrow factorization lifting package ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofibrantReplacementPacket X Q arrow factorization lifting package ledger endpoint
        bundle pkg ->
      (let Source := fun h : BHist => hsame h endpoint;
        BEDC.FKernel.NameCert.SemanticNameCert Source Source Source hsame) ∧
        UnaryHistory X ∧ UnaryHistory Q ∧ UnaryHistory arrow ∧
          UnaryHistory factorization ∧ UnaryHistory lifting ∧ UnaryHistory package ∧
            UnaryHistory ledger ∧ UnaryHistory endpoint ∧ Cont arrow factorization ledger ∧
              Cont ledger package endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  obtain ⟨xUnary, qUnary, arrowUnary, factorizationUnary, liftingUnary, packageUnary,
    ledgerRow, endpointRow, pkgRow⟩ := packet
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed arrowUnary factorizationUnary ledgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledgerUnary packageUnary endpointRow
  have cert :
      (let Source := fun h : BHist => hsame h endpoint;
        BEDC.FKernel.NameCert.SemanticNameCert Source Source Source hsame) := by
    exact {
      core := {
        carrier_inhabited := Exists.intro endpoint (hsame_refl endpoint)
        equiv_refl := by
          intro h _source
          exact hsame_refl h
        equiv_symm := by
          intro h k same
          exact hsame_symm same
        equiv_trans := by
          intro h k r sameHK sameKR
          exact hsame_trans sameHK sameKR
        carrier_respects_equiv := by
          intro h k sameHK sourceH
          exact hsame_trans (hsame_symm sameHK) sourceH
      }
      pattern_sound := by
        intro h source
        exact source
      ledger_sound := by
        intro h source
        exact source
    }
  exact And.intro cert
    (And.intro xUnary
      (And.intro qUnary
        (And.intro arrowUnary
          (And.intro factorizationUnary
            (And.intro liftingUnary
              (And.intro packageUnary
                (And.intro ledgerUnary
                  (And.intro endpointUnary
                    (And.intro ledgerRow
                      (And.intro endpointRow pkgRow))))))))))

end BEDC.Derived.CofibrantReplacementUp
