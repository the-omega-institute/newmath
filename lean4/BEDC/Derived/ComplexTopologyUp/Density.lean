import BEDC.Derived.ComplexTopologyUp

namespace BEDC.Derived.ComplexTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def ComplexTopologyDensityWitness
    (center radius point : BHist) (seq : BHist -> BHist) : Prop :=
  ∃ baseGap : BHist,
    ComplexTopologyOpenDiskGap center radius point baseGap ∧
      forall n : BHist, UnaryHistory n ->
        exists gap : BHist,
          ComplexTopologyOpenDiskGap center radius (seq n) gap ∧ Cont (seq n) gap radius

end BEDC.Derived.ComplexTopologyUp
