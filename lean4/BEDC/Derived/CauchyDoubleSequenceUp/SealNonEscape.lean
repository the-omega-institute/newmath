import BEDC.Derived.CauchyDoubleSequenceUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyDoubleSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyDoubleSequenceSealNonEscape [AskSetup] [PackageSetup]
    {array schedule tolerance diagonal completion sealRow transport route provenance
      localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDoubleSequenceCarrier array schedule tolerance diagonal completion sealRow
        transport route provenance localCert bundle pkg →
      Cont sealRow localCert consumer →
        UnaryHistory array ∧ UnaryHistory schedule ∧ UnaryHistory tolerance ∧
          UnaryHistory diagonal ∧ UnaryHistory completion ∧ UnaryHistory sealRow ∧
            UnaryHistory consumer ∧ Cont array schedule diagonal ∧
              Cont schedule tolerance diagonal ∧ Cont diagonal completion sealRow ∧
                Cont sealRow localCert consumer ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: CauchyDoubleSequenceCarrier BHist Cont PkgSig UnaryHistory
  intro carrier sealConsumer
  have arrayUnary : UnaryHistory array := carrier.left
  have scheduleUnary : UnaryHistory schedule := carrier.right.left
  have toleranceUnary : UnaryHistory tolerance := carrier.right.right.left
  have handoff :
      UnaryHistory diagonal ∧ UnaryHistory completion ∧ UnaryHistory sealRow ∧
        UnaryHistory consumer ∧ Cont array schedule diagonal ∧
          Cont schedule tolerance diagonal ∧ Cont diagonal completion sealRow ∧
            PkgSig bundle provenance pkg :=
    CauchyDoubleSequenceCarrier_diagonal_handoff carrier sealConsumer
  obtain ⟨diagonalUnary, completionUnary, sealUnary, consumerUnary, arrayScheduleRoute,
    scheduleToleranceRoute, diagonalCompletionRoute, provenancePkg⟩ := handoff
  exact
    ⟨arrayUnary, scheduleUnary, toleranceUnary, diagonalUnary, completionUnary, sealUnary,
      consumerUnary, arrayScheduleRoute, scheduleToleranceRoute, diagonalCompletionRoute,
      sealConsumer, provenancePkg⟩

theorem CauchyDoubleSequenceScopedNonescape [AskSetup] [PackageSetup]
    {array schedule tolerance diagonal completion sealRow transport route provenance
      localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDoubleSequenceCarrier array schedule tolerance diagonal completion sealRow
        transport route provenance localCert bundle pkg ->
      Cont sealRow localCert consumer ->
        SemanticNameCert
            (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row array ∨ hsame row schedule ∨ hsame row tolerance ∨
                hsame row diagonal ∨ hsame row completion ∨ hsame row sealRow ∨
                  hsame row transport ∨ hsame row route ∨ hsame row provenance ∨
                    hsame row localCert ∨ hsame row consumer)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont array schedule diagonal ∧
                Cont schedule tolerance diagonal ∧ Cont diagonal completion sealRow ∧
                  Cont sealRow localCert consumer ∧ PkgSig bundle provenance pkg)
            hsame ∧ UnaryHistory consumer := by
  -- BEDC touchpoint anchor: CauchyDoubleSequenceCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sealConsumer
  have handoff :
      UnaryHistory diagonal ∧ UnaryHistory completion ∧ UnaryHistory sealRow ∧
        UnaryHistory consumer ∧ Cont array schedule diagonal ∧
          Cont schedule tolerance diagonal ∧ Cont diagonal completion sealRow ∧
            PkgSig bundle provenance pkg :=
    CauchyDoubleSequenceCarrier_diagonal_handoff carrier sealConsumer
  obtain ⟨_diagonalUnary, _completionUnary, _sealUnary, consumerUnary, arrayScheduleRoute,
    scheduleToleranceRoute, diagonalCompletionRoute, provenancePkg⟩ := handoff
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro consumer ⟨hsame_refl consumer, consumerUnary⟩
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
                          (Or.inr
                            (Or.inr source.left)))))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, arrayScheduleRoute, scheduleToleranceRoute,
            diagonalCompletionRoute, sealConsumer, provenancePkg⟩
    }
  · exact consumerUnary

end BEDC.Derived.CauchyDoubleSequenceUp
