import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LyapunovUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LyapunovPacket [AskSetup] [PackageSetup]
    (state transition quadratic positive decrease transports routes provenance name endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory transition ∧ UnaryHistory quadratic ∧
    UnaryHistory positive ∧ UnaryHistory transports ∧ UnaryHistory provenance ∧
      Cont state transition routes ∧ Cont quadratic positive decrease ∧
        Cont decrease transports endpoint ∧ Cont endpoint provenance name ∧
          PkgSig bundle name pkg

theorem LyapunovPacket_stability_transport [AskSetup] [PackageSetup]
    {state transition quadratic positive decrease transports routes provenance name endpoint state'
      transition' quadratic' positive' decrease' transports' routes' provenance' name'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LyapunovPacket state transition quadratic positive decrease transports routes provenance name
        endpoint bundle pkg ->
      hsame state state' ->
        hsame transition transition' ->
          hsame quadratic quadratic' ->
            hsame positive positive' ->
              hsame transports transports' ->
                hsame provenance provenance' ->
                  Cont state' transition' routes' ->
                    Cont quadratic' positive' decrease' ->
                      Cont decrease' transports' endpoint' ->
                        Cont endpoint' provenance' name' ->
                          PkgSig bundle name' pkg ->
                            LyapunovPacket state' transition' quadratic' positive' decrease'
                                transports' routes' provenance' name' endpoint' bundle pkg ∧
                              hsame routes routes' ∧ hsame decrease decrease' ∧
                                hsame endpoint endpoint' ∧ hsame name name' := by
  intro packet sameState sameTransition sameQuadratic samePositive sameTransports sameProvenance
    routesRow' decreaseRow' endpointRow' nameRow' nameSig'
  obtain ⟨stateUnary, transitionUnary, quadraticUnary, positiveUnary, transportsUnary,
    provenanceUnary, routesRow, decreaseRow, endpointRow, nameRow, _nameSig⟩ := packet
  have stateUnary' : UnaryHistory state' :=
    unary_transport stateUnary sameState
  have transitionUnary' : UnaryHistory transition' :=
    unary_transport transitionUnary sameTransition
  have quadraticUnary' : UnaryHistory quadratic' :=
    unary_transport quadraticUnary sameQuadratic
  have positiveUnary' : UnaryHistory positive' :=
    unary_transport positiveUnary samePositive
  have transportsUnary' : UnaryHistory transports' :=
    unary_transport transportsUnary sameTransports
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have sameRoutes : hsame routes routes' :=
    cont_respects_hsame sameState sameTransition routesRow routesRow'
  have decreaseUnary' : UnaryHistory decrease' :=
    unary_cont_closed quadraticUnary' positiveUnary' decreaseRow'
  have sameDecrease : hsame decrease decrease' :=
    cont_respects_hsame sameQuadratic samePositive decreaseRow decreaseRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed decreaseUnary' transportsUnary' endpointRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameDecrease sameTransports endpointRow endpointRow'
  have sameName : hsame name name' :=
    cont_respects_hsame sameEndpoint sameProvenance nameRow nameRow'
  have transported :
      LyapunovPacket state' transition' quadratic' positive' decrease' transports' routes'
        provenance' name' endpoint' bundle pkg :=
    ⟨stateUnary', transitionUnary', quadraticUnary', positiveUnary', transportsUnary',
      provenanceUnary', routesRow', decreaseRow', endpointRow', nameRow', nameSig'⟩
  exact ⟨transported, sameRoutes, sameDecrease, sameEndpoint, sameName⟩

theorem LyapunovPacket_consumer_boundary [AskSetup] [PackageSetup]
    {state transition quadratic positive decrease transports routes provenance name endpoint consumer
      controlRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LyapunovPacket state transition quadratic positive decrease transports routes provenance name
        endpoint bundle pkg ->
      Cont endpoint state consumer ->
        Cont consumer quadratic controlRead ->
          PkgSig bundle controlRead pkg ->
            UnaryHistory state ∧ UnaryHistory transition ∧ UnaryHistory quadratic ∧
              UnaryHistory positive ∧ UnaryHistory decrease ∧ UnaryHistory consumer ∧
                UnaryHistory controlRead ∧ hsame routes (append state transition) ∧
                  hsame decrease (append quadratic positive) ∧
                    hsame endpoint (append decrease transports) ∧
                      hsame consumer (append endpoint state) ∧
                        hsame controlRead (append consumer quadratic) ∧
                          PkgSig bundle controlRead pkg := by
  intro packet consumerRow controlReadRow controlReadSig
  obtain ⟨stateUnary, transitionUnary, quadraticUnary, positiveUnary, transportsUnary,
    _provenanceUnary, routesRow, decreaseRow, endpointRow, _nameRow, _nameSig⟩ := packet
  have decreaseUnary : UnaryHistory decrease :=
    unary_cont_closed quadraticUnary positiveUnary decreaseRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed decreaseUnary transportsUnary endpointRow
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed endpointUnary stateUnary consumerRow
  have controlReadUnary : UnaryHistory controlRead :=
    unary_cont_closed consumerUnary quadraticUnary controlReadRow
  exact ⟨stateUnary, transitionUnary, quadraticUnary, positiveUnary, decreaseUnary, consumerUnary,
    controlReadUnary, routesRow, decreaseRow, endpointRow, consumerRow, controlReadRow,
      controlReadSig⟩

def LyapunovLedger [AskSetup] [PackageSetup]
    (state transition quadratic positive decrease transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory transition ∧ UnaryHistory quadratic ∧
    UnaryHistory positive ∧ UnaryHistory decrease ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont state transition positive ∧ Cont quadratic positive decrease ∧
          Cont decrease route transport ∧ Cont transport provenance name ∧
            PkgSig bundle name pkg

theorem LyapunovLedger_stability_transport [AskSetup] [PackageSetup]
    {state transition quadratic positive decrease transport route provenance name state'
      transition' quadratic' positive' decrease' transport' route' provenance' name' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LyapunovLedger state transition quadratic positive decrease transport route provenance name
        bundle pkg ->
      hsame state state' -> hsame transition transition' -> hsame quadratic quadratic' ->
        hsame positive positive' -> hsame decrease decrease' -> hsame route route' ->
          hsame provenance provenance' -> Cont state' transition' positive' ->
            Cont quadratic' positive' decrease' -> Cont decrease' route' transport' ->
              Cont transport' provenance' name' -> PkgSig bundle name' pkg ->
                LyapunovLedger state' transition' quadratic' positive' decrease' transport'
                    route' provenance' name' bundle pkg ∧
                  hsame transport transport' ∧ hsame name name' := by
  intro ledger sameState sameTransition sameQuadratic samePositive sameDecrease sameRoute
    sameProvenance positiveCont' decreaseCont' transportCont' nameCont' pkgSig'
  have stateUnary' : UnaryHistory state' :=
    unary_transport ledger.left sameState
  have transitionUnary' : UnaryHistory transition' :=
    unary_transport ledger.right.left sameTransition
  have quadraticUnary' : UnaryHistory quadratic' :=
    unary_transport ledger.right.right.left sameQuadratic
  have positiveUnary' : UnaryHistory positive' :=
    unary_transport ledger.right.right.right.left samePositive
  have decreaseUnary' : UnaryHistory decrease' :=
    unary_transport ledger.right.right.right.right.left sameDecrease
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame sameDecrease sameRoute
      ledger.right.right.right.right.right.right.right.right.right.right.right.left
      transportCont'
  have transportUnary' : UnaryHistory transport' :=
    unary_transport ledger.right.right.right.right.right.left sameTransport
  have routeUnary' : UnaryHistory route' :=
    unary_transport ledger.right.right.right.right.right.right.left sameRoute
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport ledger.right.right.right.right.right.right.right.left sameProvenance
  have sameName : hsame name name' :=
    cont_respects_hsame sameTransport sameProvenance
      ledger.right.right.right.right.right.right.right.right.right.right.right.right.left
      nameCont'
  have nameUnary' : UnaryHistory name' :=
    unary_transport ledger.right.right.right.right.right.right.right.right.left sameName
  exact And.intro
    (And.intro stateUnary'
      (And.intro transitionUnary'
        (And.intro quadraticUnary'
          (And.intro positiveUnary'
            (And.intro decreaseUnary'
              (And.intro transportUnary'
                (And.intro routeUnary'
                  (And.intro provenanceUnary'
                    (And.intro nameUnary'
                      (And.intro positiveCont'
                        (And.intro decreaseCont'
                          (And.intro transportCont'
                            (And.intro nameCont' pkgSig')))))))))))))
    (And.intro sameTransport sameName)

def LyapunovLedgerNameSurface [AskSetup] [PackageSetup]
    (state transition quadratic positive decrease transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) (row : BHist) : Prop :=
  row = name ∧
    LyapunovLedger state transition quadratic positive decrease transport route provenance name
      bundle pkg

theorem LyapunovLedger_namecert_obligation_surface [AskSetup] [PackageSetup]
    {state transition quadratic positive decrease transport route provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LyapunovLedger state transition quadratic positive decrease transport route provenance name
        bundle pkg ->
      SemanticNameCert
          (LyapunovLedgerNameSurface state transition quadratic positive decrease transport route
            provenance name bundle pkg)
          (LyapunovLedgerNameSurface state transition quadratic positive decrease transport route
            provenance name bundle pkg)
          (LyapunovLedgerNameSurface state transition quadratic positive decrease transport route
            provenance name bundle pkg)
          hsame ∧
        UnaryHistory state ∧ UnaryHistory transition ∧ UnaryHistory quadratic ∧
          UnaryHistory positive ∧ UnaryHistory decrease ∧ UnaryHistory transport ∧
            UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
              Cont state transition positive ∧ Cont quadratic positive decrease ∧
                Cont decrease route transport ∧ Cont transport provenance name ∧
                  PkgSig bundle name pkg := by
  intro ledger
  let Surface : BHist -> Prop :=
    LyapunovLedgerNameSurface state transition quadratic positive decrease transport route
      provenance name bundle pkg
  have sourceName : Surface name := by
    exact And.intro rfl ledger
  have core : NameCert Surface hsame := {
    carrier_inhabited := Exists.intro name sourceName
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
      intro h k same sourceH
      cases same
      exact sourceH
  }
  have semantic : SemanticNameCert Surface Surface Surface hsame := {
    core := core
    pattern_sound := by
      intro h source
      exact source
    ledger_sound := by
      intro h source
      exact source
  }
  exact And.intro semantic ledger

end BEDC.Derived.LyapunovUp
