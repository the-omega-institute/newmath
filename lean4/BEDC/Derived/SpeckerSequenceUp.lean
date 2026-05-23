import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SpeckerSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SpeckerSequenceCarrier [AskSetup] [PackageSetup]
    (regSource streamWindow dyadicLedger monotoneLedger boundedLedger realSeal transportRows
      routeRows provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory regSource ∧ UnaryHistory streamWindow ∧ UnaryHistory dyadicLedger ∧
    UnaryHistory monotoneLedger ∧ UnaryHistory boundedLedger ∧ UnaryHistory realSeal ∧
      UnaryHistory transportRows ∧ UnaryHistory routeRows ∧ UnaryHistory provenance ∧
        UnaryHistory nameRow ∧ Cont regSource streamWindow dyadicLedger ∧
          Cont dyadicLedger monotoneLedger boundedLedger ∧
            Cont boundedLedger realSeal routeRows ∧ PkgSig bundle provenance pkg

theorem SpeckerSequenceCarrier_exposure [AskSetup] [PackageSetup]
    {regSource streamWindow dyadicLedger monotoneLedger boundedLedger realSeal transportRows
      routeRows provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpeckerSequenceCarrier regSource streamWindow dyadicLedger monotoneLedger boundedLedger
        realSeal transportRows routeRows provenance nameRow bundle pkg ->
      UnaryHistory regSource ∧ UnaryHistory streamWindow ∧ UnaryHistory dyadicLedger ∧
        UnaryHistory monotoneLedger ∧ UnaryHistory boundedLedger ∧ UnaryHistory realSeal ∧
          UnaryHistory transportRows ∧ UnaryHistory routeRows ∧ UnaryHistory provenance ∧
            UnaryHistory nameRow ∧ Cont regSource streamWindow dyadicLedger ∧
              Cont dyadicLedger monotoneLedger boundedLedger ∧
                Cont boundedLedger realSeal routeRows ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier
  obtain ⟨regUnary, windowUnary, dyadicUnary, monotoneUnary, boundedUnary, realUnary,
    transportUnary, routeUnary, provenanceUnary, nameUnary, sourceWindowDyadic,
    dyadicMonotoneBounded, boundedRealRoute, provenancePkg⟩ := carrier
  exact
    ⟨regUnary, windowUnary, dyadicUnary, monotoneUnary, boundedUnary, realUnary,
      transportUnary, routeUnary, provenanceUnary, nameUnary, sourceWindowDyadic,
      dyadicMonotoneBounded, boundedRealRoute, provenancePkg⟩

theorem SpeckerSequenceClassifier_transport [AskSetup] [PackageSetup]
    {regSource streamWindow dyadicLedger monotoneLedger boundedLedger realSeal transportRows
      routeRows provenance nameRow regSource' streamWindow' dyadicLedger' monotoneLedger'
      boundedLedger' realSeal' transportRows' routeRows' provenance' nameRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpeckerSequenceCarrier regSource streamWindow dyadicLedger monotoneLedger boundedLedger
        realSeal transportRows routeRows provenance nameRow bundle pkg →
      hsame regSource regSource' →
        hsame streamWindow streamWindow' →
          hsame dyadicLedger dyadicLedger' →
            hsame monotoneLedger monotoneLedger' →
              hsame boundedLedger boundedLedger' →
                hsame realSeal realSeal' →
                  hsame transportRows transportRows' →
                    hsame provenance provenance' →
                      hsame nameRow nameRow' →
                        Cont regSource' streamWindow' dyadicLedger' →
                          Cont dyadicLedger' monotoneLedger' boundedLedger' →
                            Cont boundedLedger' realSeal' routeRows' →
                              PkgSig bundle provenance' pkg →
                                SpeckerSequenceCarrier regSource' streamWindow'
                                  dyadicLedger' monotoneLedger' boundedLedger' realSeal'
                                  transportRows' routeRows' provenance' nameRow' bundle
                                  pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameReg sameWindow sameDyadic sameMonotone sameBounded sameReal
    sameTransport sameProvenance sameName sourceWindowDyadic' dyadicMonotoneBounded'
    boundedRealRoute' provenancePkg'
  obtain ⟨regUnary, windowUnary, dyadicUnary, monotoneUnary, boundedUnary, realUnary,
    transportUnary, _routeUnary, provenanceUnary, nameUnary, _sourceWindowDyadic,
    _dyadicMonotoneBounded, _boundedRealRoute, _provenancePkg⟩ := carrier
  have regUnary' : UnaryHistory regSource' :=
    unary_transport regUnary sameReg
  have windowUnary' : UnaryHistory streamWindow' :=
    unary_transport windowUnary sameWindow
  have dyadicUnary' : UnaryHistory dyadicLedger' :=
    unary_transport dyadicUnary sameDyadic
  have monotoneUnary' : UnaryHistory monotoneLedger' :=
    unary_transport monotoneUnary sameMonotone
  have boundedUnary' : UnaryHistory boundedLedger' :=
    unary_transport boundedUnary sameBounded
  have realUnary' : UnaryHistory realSeal' :=
    unary_transport realUnary sameReal
  have transportUnary' : UnaryHistory transportRows' :=
    unary_transport transportUnary sameTransport
  have routeUnary' : UnaryHistory routeRows' :=
    unary_cont_closed boundedUnary' realUnary' boundedRealRoute'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have nameUnary' : UnaryHistory nameRow' :=
    unary_transport nameUnary sameName
  exact
    ⟨regUnary', windowUnary', dyadicUnary', monotoneUnary', boundedUnary', realUnary',
      transportUnary', routeUnary', provenanceUnary', nameUnary', sourceWindowDyadic',
      dyadicMonotoneBounded', boundedRealRoute', provenancePkg'⟩

theorem SpeckerSequence_monotone_bounded_ledger [AskSetup] [PackageSetup]
    {regSource streamWindow dyadicLedger monotoneLedger boundedLedger realSeal transportRows
      routeRows provenance nameRow sealRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpeckerSequenceCarrier regSource streamWindow dyadicLedger monotoneLedger boundedLedger
        realSeal transportRows routeRows provenance nameRow bundle pkg ->
      Cont (append regSource streamWindow) dyadicLedger monotoneLedger ->
        Cont monotoneLedger boundedLedger sealRoute ->
          Cont sealRoute realSeal routeRows ->
            PkgSig bundle sealRoute pkg ->
              UnaryHistory regSource ∧ UnaryHistory streamWindow ∧
                UnaryHistory dyadicLedger ∧ UnaryHistory monotoneLedger ∧
                  UnaryHistory boundedLedger ∧ UnaryHistory realSeal ∧
                    UnaryHistory sealRoute ∧ Cont regSource streamWindow dyadicLedger ∧
                      Cont (append regSource streamWindow) dyadicLedger monotoneLedger ∧
                        Cont monotoneLedger boundedLedger sealRoute ∧
                          Cont sealRoute realSeal routeRows ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle sealRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceDyadicMonotone monotoneBoundedSeal sealRealRoute sealPkg
  obtain ⟨regUnary, windowUnary, dyadicUnary, monotoneUnary, boundedUnary, realUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, sourceWindowDyadic,
    _dyadicMonotoneBounded, _boundedRealRoute, provenancePkg⟩ := carrier
  have sealUnary : UnaryHistory sealRoute :=
    unary_cont_closed monotoneUnary boundedUnary monotoneBoundedSeal
  exact
    ⟨regUnary, windowUnary, dyadicUnary, monotoneUnary, boundedUnary, realUnary, sealUnary,
      sourceWindowDyadic, sourceDyadicMonotone, monotoneBoundedSeal, sealRealRoute,
      provenancePkg, sealPkg⟩

end BEDC.Derived.SpeckerSequenceUp
