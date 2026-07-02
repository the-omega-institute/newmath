import BEDC.Derived.FullAxisRealRefusalUp.TasteGate

namespace BEDC.Derived.FullAxisRealRefusalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

theorem FullAxisRealRefusal_non_escape (q : FullAxisRealRefusalUp) :
    ∃ fullAxis refusal cannotClaim transport route provenance name : BHist,
      q =
          FullAxisRealRefusalUp.mk fullAxis refusal cannotClaim transport route provenance name ∧
        fullAxisRealRefusalFromEventFlow (fullAxisRealRefusalToEventFlow q) = some q ∧
          fullAxisRealRefusalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases q with
  | mk fullAxis refusal cannotClaim transport route provenance name =>
      exact
        ⟨fullAxis, refusal, cannotClaim, transport, route, provenance, name, rfl,
          FullAxisRealRefusalTasteGate_single_carrier_alignment.right.left
            (FullAxisRealRefusalUp.mk fullAxis refusal cannotClaim transport route provenance name),
          rfl⟩

end BEDC.Derived.FullAxisRealRefusalUp
