import BEDC.FKernel.Bundle
import BEDC.FKernel.Ask
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived

def ConstructiveHeineBorelIntervalUp : Type :=
  Unit

end BEDC.Derived

namespace BEDC.Derived.ConstructiveHeineBorelIntervalUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Ask
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ConstructiveHeineBorelIntervalCarrier [AskSetup] [PackageSetup]
    (I D R S E M U H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory I ∧
    UnaryHistory D ∧
      UnaryHistory R ∧
        UnaryHistory S ∧
          UnaryHistory E ∧
            UnaryHistory M ∧
              UnaryHistory U ∧
                UnaryHistory H ∧
                  UnaryHistory C ∧
                    UnaryHistory P ∧
                      UnaryHistory N ∧ PkgSig bundle P pkg

end BEDC.Derived.ConstructiveHeineBorelIntervalUp
