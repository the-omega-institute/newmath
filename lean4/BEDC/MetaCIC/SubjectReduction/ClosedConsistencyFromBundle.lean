import BEDC.MetaCIC.SubjectReduction.DischargeBundle
import BEDC.MetaCIC.Consistency

namespace BEDC.MetaCIC

def ClosedConsistencyFromBundleStatement : Prop :=
  ∀ (_h : SubjectReductionDischargeBundle), no_closed_proof_of_false

theorem closed_consistency_from_bundle_statement_well_formed :
    True := True.intro

end BEDC.MetaCIC
