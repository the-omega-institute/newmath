import BEDC.Derived.KanExtensionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.KanExtensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KanExtensionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {C D E J F L eta U V H R P N _comparison mediator composite namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory C ->
      UnaryHistory D ->
        UnaryHistory E ->
          UnaryHistory J ->
            UnaryHistory F ->
              UnaryHistory L ->
                UnaryHistory eta ->
                  UnaryHistory U ->
                    UnaryHistory V ->
                      UnaryHistory H ->
                        UnaryHistory R ->
                          UnaryHistory N ->
                            Cont eta U mediator ->
                              Cont mediator J composite ->
                                Cont composite R namedRead ->
                                  PkgSig bundle P pkg ->
                                    PkgSig bundle N pkg ->
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row namedRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row C ∨ hsame row D ∨
                                              hsame row E ∨ hsame row J ∨
                                                hsame row F ∨ hsame row L ∨
                                                  hsame row eta ∨ hsame row U ∨
                                                    hsame row V ∨ hsame row namedRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont eta U mediator ∧
                                              Cont mediator J composite ∧
                                                Cont composite R namedRead ∧
                                                  PkgSig bundle P pkg ∧
                                                    PkgSig bundle N pkg)
                                          hsame ∧
                                        UnaryHistory mediator ∧
                                          UnaryHistory composite ∧
                                            UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro cUnary dUnary eUnary jUnary fUnary lUnary etaUnary uUnary vUnary hUnary rUnary
    nUnary etaUniversalRoute mediatorFunctorRoute compositeReplayRoute provenancePkg namePkg
  have mediatorUnary : UnaryHistory mediator :=
    unary_cont_closed etaUnary uUnary etaUniversalRoute
  have compositeUnary : UnaryHistory composite :=
    unary_cont_closed mediatorUnary jUnary mediatorFunctorRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed compositeUnary rUnary compositeReplayRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left))))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, etaUniversalRoute, mediatorFunctorRoute, compositeReplayRoute,
            provenancePkg, namePkg⟩
    }
  · exact ⟨mediatorUnary, compositeUnary, namedReadUnary⟩

end BEDC.Derived.KanExtensionUp
