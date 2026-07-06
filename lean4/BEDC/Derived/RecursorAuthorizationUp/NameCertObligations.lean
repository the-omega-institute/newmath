import BEDC.Derived.RecursorAuthorizationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.RecursorAuthorizationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem RecursorAuthorization_namecert_obligations
    (x : RecursorAuthorizationUp) :
    ∃ inductiveName signature recursor motive branches descent transports continuations
        provenance name signatureRoute branchRoute outputRoute : BHist,
      x =
          RecursorAuthorizationUp.mk inductiveName signature recursor motive branches descent
            transports continuations provenance name ∧
        Cont signature recursor signatureRoute ∧
          Cont motive branches branchRoute ∧
            Cont branchRoute descent outputRoute ∧
              recursorAuthorizationFromEventFlow (recursorAuthorizationToEventFlow x) =
                some x := by
  -- BEDC touchpoint anchor: BHist BMark Cont
  cases x with
  | mk inductiveName signature recursor motive branches descent transports continuations
      provenance name =>
      exact
        ⟨inductiveName, signature, recursor, motive, branches, descent, transports,
          continuations, provenance, name, append signature recursor, append motive branches,
          append (append motive branches) descent, rfl, rfl, rfl, rfl,
          RecursorAuthorizationTasteGate_single_carrier_alignment.right.left
            (RecursorAuthorizationUp.mk inductiveName signature recursor motive branches
              descent transports continuations provenance name)⟩

end BEDC.Derived.RecursorAuthorizationUp
