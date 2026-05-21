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

end BEDC.Derived.SpeckerSequenceUp
