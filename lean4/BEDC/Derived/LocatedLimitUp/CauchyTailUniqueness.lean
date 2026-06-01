import BEDC.Derived.LocatedLimitUp.RealSealRoute

namespace BEDC.Derived.LocatedLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem LocatedLimitCarrier_cauchy_tail_uniqueness [AskSetup] [PackageSetup]
    {sequence modulus schedule readback sealRow transport replay provenance name sequence' modulus'
      schedule' readback' sealRow' transport' replay' provenance' name' leftTail rightTail :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedLimitCarrier sequence modulus schedule readback sealRow transport replay provenance name
        bundle pkg →
      LocatedLimitCarrier sequence' modulus' schedule' readback' sealRow' transport' replay'
        provenance' name' bundle pkg →
        locatedLimitFields
            (LocatedLimitUp.mk sequence modulus schedule readback sealRow transport replay provenance
              name) =
          locatedLimitFields
            (LocatedLimitUp.mk sequence' modulus' schedule' readback' sealRow' transport' replay'
              provenance' name') →
          Cont sequence modulus leftTail →
            Cont sequence' modulus' rightTail →
              hsame leftTail rightTail →
                hsame sequence sequence' ∧ hsame modulus modulus' := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg LocatedLimitCarrier
  intro _leftCarrier _rightCarrier fieldsSame _leftTailRoute _rightTailRoute _sameTails
  change
      [sequence, modulus, schedule, readback, sealRow, transport, replay, provenance, name] =
        [sequence', modulus', schedule', readback', sealRow', transport', replay', provenance',
          name'] at fieldsSame
  injection fieldsSame with sameSequence tailSame
  injection tailSame with sameModulus _tailRest
  exact ⟨sameSequence, sameModulus⟩

end BEDC.Derived.LocatedLimitUp
