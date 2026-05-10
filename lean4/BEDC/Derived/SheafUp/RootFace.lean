import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem SheafRootFaceRead_locality_gluing_refinement_inversion {common germA : BHist} :
    SheafRootFaceRead common germA SheafRootFaceLanding.localityGluingRefinement ->
      ∃ sectA : BHist, ∃ sectB : BHist, ∃ germB : BHist,
        Cont common sectA germA ∧ Cont common sectB germB ∧ hsame germA germB := by
  intro read
  cases read with
  | localityGluingRefinement sectionA sectionB sameGerms =>
      exact Exists.intro _
        (Exists.intro _
          (Exists.intro _
            (And.intro sectionA (And.intro sectionB sameGerms))))

end BEDC.Derived.SheafUp
