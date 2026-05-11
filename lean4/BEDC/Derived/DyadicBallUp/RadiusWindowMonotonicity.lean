import BEDC.Derived.DyadicBallUp

namespace BEDC.Derived.DyadicBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicBallFiniteEnclosure_radius_window_monotonicity [AskSetup] [PackageSetup]
    {center radius schedule observation containment transportWindow regWindow certRow center'
      radius' schedule' observation' containment' transportWindow' regWindow' certRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicBallFiniteEnclosure center radius schedule observation containment transportWindow
        regWindow certRow bundle pkg ->
      hsame center center' ->
        UnaryHistory radius' ->
          hsame schedule schedule' ->
            hsame observation observation' ->
              hsame containment containment' ->
                Cont center' radius' transportWindow' ->
                  Cont observation' containment' regWindow' ->
                    Cont transportWindow' regWindow' certRow' ->
                      PkgSig bundle regWindow' pkg ->
                        DyadicBallFiniteEnclosure center' radius' schedule' observation'
                            containment' transportWindow' regWindow' certRow' bundle pkg ∧
                          Cont center' radius' transportWindow' ∧
                            Cont observation' containment' regWindow' ∧
                              PkgSig bundle regWindow' pkg := by
  intro enclosure sameCenter radiusUnary' sameSchedule sameObservation sameContainment
    transportWindowRow' regWindowRow' certRowRoute' pkgRow'
  obtain ⟨centerUnary, _radiusUnary, scheduleUnary, observationUnary, containmentUnary,
    _transportUnary, _regUnary, _certUnary, _transportWindowRow, _regWindowRow,
    _certRowRoute, _pkgRow⟩ := enclosure
  have centerUnary' : UnaryHistory center' :=
    unary_transport centerUnary sameCenter
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have observationUnary' : UnaryHistory observation' :=
    unary_transport observationUnary sameObservation
  have containmentUnary' : UnaryHistory containment' :=
    unary_transport containmentUnary sameContainment
  have transportWindowUnary' : UnaryHistory transportWindow' :=
    unary_cont_closed centerUnary' radiusUnary' transportWindowRow'
  have regWindowUnary' : UnaryHistory regWindow' :=
    unary_cont_closed observationUnary' containmentUnary' regWindowRow'
  have certRowUnary' : UnaryHistory certRow' :=
    unary_cont_closed transportWindowUnary' regWindowUnary' certRowRoute'
  exact
    ⟨⟨centerUnary', radiusUnary', scheduleUnary', observationUnary', containmentUnary',
        transportWindowUnary', regWindowUnary', certRowUnary', transportWindowRow',
        regWindowRow', certRowRoute', pkgRow'⟩,
      transportWindowRow', regWindowRow', pkgRow'⟩

end BEDC.Derived.DyadicBallUp
