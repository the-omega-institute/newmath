import BEDC.Derived.RecursorInducedNameCertUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.RecursorInducedNameCertUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem RecursorInducedNameCert_namecert_obligation_surface
    (x : RecursorInducedNameCertUp) :
    ∃ signature motive branch output audit transport continuation provenance name branchRoute
        auditRoute publicRoute : BHist,
      x =
          RecursorInducedNameCertUp.mk signature motive branch output audit transport
            continuation provenance name ∧
        Cont motive branch branchRoute ∧
          Cont output audit auditRoute ∧
            Cont branchRoute auditRoute publicRoute ∧
              recursorInducedNameCertFromEventFlow (recursorInducedNameCertToEventFlow x) =
                some x := by
  -- BEDC touchpoint anchor: BHist BMark Cont
  cases x with
  | mk signature motive branch output audit transport continuation provenance name =>
      exact
        ⟨signature, motive, branch, output, audit, transport, continuation, provenance, name,
          append motive branch, append output audit, append (append motive branch)
            (append output audit), rfl, rfl, rfl, rfl,
          RecursorInducedNameCertTasteGate_single_carrier_alignment.right.left
            (RecursorInducedNameCertUp.mk signature motive branch output audit transport
              continuation provenance name)⟩

end BEDC.Derived.RecursorInducedNameCertUp
