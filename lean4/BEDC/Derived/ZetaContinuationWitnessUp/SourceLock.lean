import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def ZetaContinuationWitnessSourceLock [AskSetup] [PackageSetup]
    (basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      sourceRead continuationRead publicRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
      routes provenance name bundle pkg ∧
    Cont basic eta analytic ∧
      Cont analytic functional transports ∧
        Cont pole zeroLedger gamma ∧
          Cont transports routes provenance ∧
            Cont basic analytic sourceRead ∧
              Cont sourceRead transports continuationRead ∧
                Cont continuationRead name publicRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg

end BEDC.Derived.ZetaContinuationWitnessUp
