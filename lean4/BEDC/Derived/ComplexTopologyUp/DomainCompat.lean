import BEDC.Derived.ComplexTopologyUp.Density

namespace BEDC.Derived.ComplexTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def ComplexTopologyDomainCompat (D1 D2 overlap : BHist -> Prop)
    (center radius point gap : BHist) : Prop :=
  ComplexTopologyOpenSet D1 ∧ ComplexTopologyOpenSet D2 ∧ ComplexTopologyOpenSet overlap ∧
    ComplexTopologyOpenDiskGap center radius point gap ∧ Cont point gap radius ∧
      overlap point ∧ D1 point ∧ D2 point ∧
        (forall {z : BHist}, overlap z -> D1 z ∧ D2 z) ∧
          ComplexTopologyDensityWitness center radius point (fun _ : BHist => point)

end BEDC.Derived.ComplexTopologyUp
