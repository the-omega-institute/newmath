import BEDC.MetaCIC.SubjectReduction.DischargeBundle
import BEDC.MetaCIC.SubjectReduction.ClosedDischarge
import BEDC.MetaCIC.SubjectReduction.ClosedBinderDischarge

namespace BEDC.MetaCIC

theorem not_appArgTypeStable : ¬ AppArgTypeStable := by
  intro h
  cases appArgTypeStable_closed_counterexample with
  | intro f rest =>
      cases rest with
      | intro a rest =>
          cases rest with
          | intro a' rest =>
              cases rest with
              | intro dom rest =>
                  cases rest with
                  | intro cod hpack =>
                      exact hpack.right.right.right.right.right.right
                        (h hpack.left hpack.right.left hpack.right.right.left)

theorem not_lamDomainSubjectReduction : ¬ LamDomainSubjectReduction := by
  intro h
  exact closedLamDomainTarget_not_typed
    (h closedLamDomainSource_typed closedReducingType_step)

theorem not_piDomainSubjectReduction : ¬ PiDomainSubjectReduction := by
  intro h
  exact closedPiDomainTarget_not_typed
    (h closedPiDomainSource_typed closedReducingType_step)

theorem not_subjectReductionDischargeBundle :
    ¬ SubjectReductionDischargeBundle := by
  intro h
  exact not_appArgTypeStable h.appArgTypeStable

end BEDC.MetaCIC
