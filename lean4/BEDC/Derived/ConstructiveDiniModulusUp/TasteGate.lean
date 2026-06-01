import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ConstructiveDiniModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ConstructiveDiniModulusCarrier [AskSetup] [PackageSetup]
    (K F L N Q W S R E G M H C P A : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory K ∧ UnaryHistory F ∧ UnaryHistory L ∧ UnaryHistory N ∧
    UnaryHistory Q ∧ UnaryHistory W ∧ UnaryHistory S ∧ UnaryHistory R ∧
      UnaryHistory E ∧ UnaryHistory G ∧ UnaryHistory M ∧ UnaryHistory H ∧
        UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory A ∧ Cont K N Q ∧
          Cont L W S ∧ Cont R E G ∧ Cont G M C ∧ PkgSig bundle P pkg

end BEDC.Derived.ConstructiveDiniModulusUp
