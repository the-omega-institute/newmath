import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FrechetFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FrechetFilterCarrier [AskSetup] [PackageSetup]
    (threshold tail schedule metric filterBase cauchyHandoff readback realSeal
      transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory threshold ∧ UnaryHistory tail ∧ UnaryHistory schedule ∧
    UnaryHistory metric ∧ UnaryHistory filterBase ∧ UnaryHistory cauchyHandoff ∧
      UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
        UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
          Cont threshold tail schedule ∧ Cont schedule metric filterBase ∧
            Cont filterBase cauchyHandoff readback ∧ Cont readback realSeal replay ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

end BEDC.Derived.FrechetFilterUp
