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

theorem ComplexTopologyOpenDiskGap_density_witness_with_boundary
    {center radius point gap : BHist} :
    ComplexTopologyOpenDiskGap center radius point gap ->
      ComplexTopologyDensityWitness center radius point (fun _n : BHist => point) ∧
        (forall n : BHist, UnaryHistory n ->
          exists g : BHist,
            ComplexTopologyOpenDiskGap center radius point g ∧ Cont point g radius) := by
  intro disk
  have boundary : Cont point gap radius := disk.right.right.right.right
  exact And.intro
    (Exists.intro gap
      (And.intro disk
        (fun _n _unary => Exists.intro gap (And.intro disk boundary))))
    (fun _n _unary => Exists.intro gap (And.intro disk boundary))

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
