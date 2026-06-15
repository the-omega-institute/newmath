import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.IntervalHalvingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def IntervalHalvingCarrier [AskSetup] [PackageSetup]
    (left right midpoint chosenHalf radius streamWindow regularReadback realSeal transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory midpoint ∧ UnaryHistory chosenHalf ∧
    UnaryHistory radius ∧ UnaryHistory streamWindow ∧ UnaryHistory regularReadback ∧
      UnaryHistory realSeal ∧ UnaryHistory transport ∧ hsame transport (append left right) ∧
        Cont left right midpoint ∧ Cont midpoint chosenHalf radius ∧
          Cont radius streamWindow regularReadback ∧ Cont regularReadback realSeal replay ∧
            Cont transport replay provenance ∧ PkgSig bundle localName pkg

end BEDC.Derived.IntervalHalvingUp
