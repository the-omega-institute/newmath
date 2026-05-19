import BEDC.Derived.KernelInductiveAcceptanceUp.TasteGate

namespace BEDC.Derived.KernelInductiveAcceptanceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem KernelInductiveAcceptanceUp_hsame_transport_scope
    {D S E P R _H _C Q N D' S' E' P' R' Q' N' sigRead elimRead refuseRead
      envRead : BHist} :
    hsame D D' ->
      hsame S S' ->
        hsame E E' ->
          hsame P P' ->
            hsame R R' ->
              hsame Q Q' ->
                hsame N N' ->
                  UnaryHistory D ->
                    UnaryHistory S ->
                      UnaryHistory E ->
                        UnaryHistory P ->
                          UnaryHistory R ->
                            Cont D S sigRead ->
                              Cont S E elimRead ->
                                Cont P R refuseRead ->
                                  Cont E R envRead ->
                                    UnaryHistory D' ∧ UnaryHistory S' ∧
                                      UnaryHistory E' ∧ UnaryHistory P' ∧
                                        UnaryHistory R' ∧ Cont D' S' sigRead ∧
                                          Cont S' E' elimRead ∧
                                            Cont P' R' refuseRead ∧
                                              Cont E' R' envRead ∧ hsame N' N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro sameD sameS sameE sameP sameR _sameQ sameN declarationUnary signaturesUnary
    eliminatorsUnary positivityUnary recursionUnary declarationSignaturesRead
    signaturesEliminatorsRead positivityRecursionRead eliminatorsRecursionRead
  cases sameD
  cases sameS
  cases sameE
  cases sameP
  cases sameR
  cases sameN
  exact
    ⟨declarationUnary, signaturesUnary, eliminatorsUnary, positivityUnary, recursionUnary,
      declarationSignaturesRead, signaturesEliminatorsRead, positivityRecursionRead,
      eliminatorsRecursionRead, hsame_refl N⟩

end BEDC.Derived.KernelInductiveAcceptanceUp
