import BEDC.Derived.CauchyDoubleSequenceUp

namespace BEDC.Derived.CauchyDoubleSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyDoubleSequenceDiagonalTailEnvelope [AskSetup] [PackageSetup]
    {array schedule tolerance diagonal completion sealRow transport route provenance
      localCert schedule2 tolerance2 diagonal2 sealRow2 consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDoubleSequenceCarrier array schedule tolerance diagonal completion sealRow transport
        route provenance localCert bundle pkg →
      hsame schedule schedule2 →
        hsame tolerance tolerance2 →
          Cont array schedule2 diagonal2 →
            Cont schedule2 tolerance2 diagonal2 →
              Cont diagonal2 completion sealRow2 →
                Cont sealRow2 localCert consumer →
                  SemanticNameCert
                      (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row array ∨ hsame row schedule2 ∨ hsame row tolerance2 ∨
                          hsame row diagonal2 ∨ hsame row sealRow2 ∨ hsame row consumer)
                      (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
                      hsame ∧
                    UnaryHistory consumer ∧ hsame sealRow sealRow2 ∧
                      PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: CauchyDoubleSequenceCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sameSchedule sameTolerance arraySchedule2 scheduleTolerance2
    diagonalCompletion2 sealConsumer2
  have tail :
      UnaryHistory schedule2 ∧ UnaryHistory tolerance2 ∧ UnaryHistory diagonal2 ∧
        UnaryHistory sealRow2 ∧ UnaryHistory consumer ∧ hsame sealRow sealRow2 ∧
          PkgSig bundle provenance pkg :=
    CauchyDoubleSequenceCarrier_cofinal_tail_stability carrier sameSchedule sameTolerance
      arraySchedule2 scheduleTolerance2 diagonalCompletion2 sealConsumer2
  obtain ⟨_scheduleUnary, _toleranceUnary, _diagonalUnary, _sealUnary, consumerUnary,
    sameSealRow, provenancePkg⟩ := tail
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, provenancePkg⟩
    }
  · exact ⟨consumerUnary, sameSealRow, provenancePkg⟩

end BEDC.Derived.CauchyDoubleSequenceUp
