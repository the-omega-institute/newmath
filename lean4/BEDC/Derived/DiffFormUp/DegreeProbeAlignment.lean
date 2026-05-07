import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist

theorem DiffFormDegreeProbeAligned_empty_iff {d : BHist} :
    DegreeProbeAligned d (ProbeBundle.Bnil : ProbeBundle BHist) ↔ hsame d BHist.Empty := by
  constructor
  · intro aligned
    cases aligned with
    | nil =>
        rfl
  · intro sameDegree
    cases sameDegree
    exact DegreeProbeAligned.nil

end BEDC.Derived.DiffFormUp
