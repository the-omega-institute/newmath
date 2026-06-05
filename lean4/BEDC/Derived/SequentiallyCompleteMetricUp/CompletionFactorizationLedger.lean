import BEDC.Derived.SequentiallyCompleteMetricUp.NameCertObligations
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SequentiallyCompleteMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentiallyCompleteMetricCompletionFactorizationLedger [AskSetup] [PackageSetup]
    {X S M L D H C P N sequenceRead modulusRead limitRead distanceRead replayRead
      completeRead metricCompletionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentiallyCompleteMetricCarrier X S M L D H C P N bundle pkg ->
      Cont X S sequenceRead ->
        Cont sequenceRead M modulusRead ->
          Cont modulusRead L limitRead ->
            Cont limitRead D distanceRead ->
              Cont distanceRead C replayRead ->
                Cont replayRead N completeRead ->
                  Cont completeRead P metricCompletionRead ->
                    PkgSig bundle P pkg ->
                      PkgSig bundle metricCompletionRead pkg ->
                        SemanticNameCert
                            (fun row : BHist =>
                              hsame row metricCompletionRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row X ∨ hsame row S ∨ hsame row M ∨
                                hsame row L ∨ hsame row D ∨ hsame row completeRead ∨
                                  hsame row metricCompletionRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont X S sequenceRead ∧
                                Cont sequenceRead M modulusRead ∧
                                  Cont modulusRead L limitRead ∧
                                    Cont limitRead D distanceRead ∧
                                      Cont distanceRead C replayRead ∧
                                        Cont replayRead N completeRead ∧
                                          Cont completeRead P metricCompletionRead ∧
                                            PkgSig bundle P pkg ∧
                                              PkgSig bundle metricCompletionRead pkg)
                            hsame ∧
                          UnaryHistory completeRead ∧ UnaryHistory metricCompletionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier sequenceRoute modulusRoute limitRoute distanceRoute replayRoute completeRoute
    metricCompletionRoute provenancePkg metricCompletionPkg
  obtain ⟨xUnary, sUnary, mUnary, lUnary, dUnary, _hUnary, cUnary, pUnary, nUnary,
    _carrierSequenceRoute, _carrierLedgerRoute, _transportName, _carrierProvenancePkg⟩ :=
      carrier
  have sequenceUnary : UnaryHistory sequenceRead :=
    unary_cont_closed xUnary sUnary sequenceRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed sequenceUnary mUnary modulusRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed modulusUnary lUnary limitRoute
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed limitUnary dUnary distanceRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed distanceUnary cUnary replayRoute
  have completeUnary : UnaryHistory completeRead :=
    unary_cont_closed replayUnary nUnary completeRoute
  have metricCompletionUnary : UnaryHistory metricCompletionRead :=
    unary_cont_closed completeUnary pUnary metricCompletionRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row metricCompletionRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row X ∨ hsame row S ∨ hsame row M ∨ hsame row L ∨ hsame row D ∨
            hsame row completeRead ∨ hsame row metricCompletionRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont X S sequenceRead ∧ Cont sequenceRead M modulusRead ∧
            Cont modulusRead L limitRead ∧ Cont limitRead D distanceRead ∧
              Cont distanceRead C replayRead ∧ Cont replayRead N completeRead ∧
                Cont completeRead P metricCompletionRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle metricCompletionRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro metricCompletionRead
          ⟨hsame_refl metricCompletionRead, metricCompletionUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sequenceRoute, modulusRoute, limitRoute, distanceRoute,
          replayRoute, completeRoute, metricCompletionRoute, provenancePkg,
          metricCompletionPkg⟩
  }
  exact ⟨cert, completeUnary, metricCompletionUnary⟩

end BEDC.Derived.SequentiallyCompleteMetricUp
