import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist

theorem DiffFormZeroDegree_empty_probe_exhaustion {probe : BHist} :
    InBundle probe (ProbeBundle.Bnil : ProbeBundle BHist) -> False := by
  intro probeIn
  exact inBundle_nil_elim probeIn

end BEDC.Derived.DiffFormUp
