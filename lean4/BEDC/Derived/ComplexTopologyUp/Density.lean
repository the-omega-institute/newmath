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

theorem ComplexTopologyOpenDiskGap_constant_density_witness
    {center radius point gap : BHist} :
    ComplexTopologyOpenDiskGap center radius point gap ->
      ComplexTopologyDensityWitness center radius point (fun _ : BHist => point) ∧
        Cont point gap radius := by
  intro disk
  exact And.intro
    (Exists.intro gap
      (And.intro disk
        (by
          intro n _unaryN
          exact Exists.intro gap (And.intro disk disk.right.right.right.right))))
    disk.right.right.right.right

end BEDC.Derived.ComplexTopologyUp
