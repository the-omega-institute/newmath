import BEDC.Derived.UniformCauchyCriterionUp.RealCompletionExitExhaustion
import BEDC.FKernel.NameCert

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_terminal_real_completion_lock [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailRead
      sealRead sealBudgetRead completionRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index tail tailRead →
        Cont tail sealRow sealRead →
          Cont tailRead sealRead sealBudgetRead →
            Cont sealBudgetRead provenance completionRead →
              PkgSig bundle tailRead pkg →
                PkgSig bundle sealRead pkg →
                  PkgSig bundle sealBudgetRead pkg →
                    PkgSig bundle completionRead pkg →
                      SemanticNameCert
                        (fun row : BHist =>
                          UniformCauchyCriterionPacket index windows modulus tolerance tail
                              sealRow transports routes provenance name bundle pkg ∧
                            hsame row completionRead)
                        (fun row : BHist =>
                          Cont index tail tailRead ∧ Cont tail sealRow sealRead ∧
                            Cont tailRead sealRead sealBudgetRead ∧
                              Cont sealBudgetRead provenance row)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle completionRead pkg ∧
                            (Cont sealBudgetRead (BHist.e0 hostTail) tailRead → False) ∧
                              (Cont sealBudgetRead (BHist.e1 hostTail) tailRead → False))
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet indexTailRead tailSealRead readSealBudget budgetProvenanceCompletion
    _tailReadPkg _sealReadPkg _budgetPkg completionPkg
  have packetSource := packet
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, _namePkg⟩ := packet
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tailUnary indexTailRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have budgetUnary : UnaryHistory sealBudgetRead :=
    unary_cont_closed tailReadUnary sealReadUnary readSealBudget
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed budgetUnary provenanceUnary budgetProvenanceCompletion
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead
          (And.intro packetSource (hsame_refl completionRead))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨indexTailRead, tailSealRead, readSealBudget,
          cont_result_hsame_transport budgetProvenanceCompletion (hsame_symm source.right)⟩
    ledger_sound := by
      intro _row source
      exact
        ⟨unary_transport completionUnary (hsame_symm source.right), completionPkg,
          (fun hostReturn =>
            cont_mutual_extension_right_tail_absurd.left readSealBudget hostReturn),
          (fun hostReturn =>
            cont_mutual_extension_right_tail_absurd.right readSealBudget hostReturn)⟩
  }

end BEDC.Derived.UniformCauchyCriterionUp
