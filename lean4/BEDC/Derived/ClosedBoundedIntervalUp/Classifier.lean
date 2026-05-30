import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedBoundedIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def ClosedBoundedIntervalClassifier [AskSetup] [PackageSetup]
    (lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported lower2 upper2 order2 rational2 dyadic2 stream2 readback2 sealRow2
      transport2 replay2 provenance2 localName2 exported2 : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg ClosedBoundedIntervalPacket
  BEDC.Derived.ClosedboundedintervalUp.ClosedBoundedIntervalPacket lower upper order rational
      dyadic stream readback sealRow transport replay provenance localName exported bundle pkg ∧
    BEDC.Derived.ClosedboundedintervalUp.ClosedBoundedIntervalPacket lower2 upper2 order2
      rational2 dyadic2 stream2 readback2 sealRow2 transport2 replay2 provenance2 localName2
      exported2 bundle pkg ∧
      hsame lower lower2 ∧ hsame upper upper2 ∧ hsame order order2 ∧
        hsame rational rational2 ∧ hsame dyadic dyadic2 ∧ hsame stream stream2 ∧
          hsame readback readback2 ∧ hsame sealRow sealRow2

end BEDC.Derived.ClosedBoundedIntervalUp
