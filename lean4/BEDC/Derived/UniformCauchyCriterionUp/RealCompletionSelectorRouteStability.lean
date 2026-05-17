import BEDC.Derived.UniformCauchyCriterionUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_real_completion_selector_route_stability [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailRead sealRead
      sealBudgetRead completionRead replacementRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail tailRead ->
        Cont tail sealRow sealRead ->
          Cont tailRead sealRead sealBudgetRead ->
            Cont sealBudgetRead provenance completionRead ->
              hsame replacementRead completionRead ->
                PkgSig bundle completionRead pkg ->
                  PkgSig bundle replacementRead pkg ->
                    SemanticNameCert
                      (fun row : BHist =>
                        UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow
                          transports routes provenance name bundle pkg ∧ hsame row replacementRead)
                      (fun row : BHist =>
                        Cont sealBudgetRead provenance row ∧ hsame row replacementRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle replacementRead pkg ∧
                          (Cont sealBudgetRead (BHist.e0 hostTail) tailRead -> False) ∧
                            (Cont sealBudgetRead (BHist.e1 hostTail) tailRead -> False))
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet indexTailRead tailSealRead readSealBudget budgetProvenanceCompletion
    replacementCompletion _completionPkg replacementPkg
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, _namePkg⟩ := packet
  let packetWitness :
      UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
          provenance name bundle pkg :=
    ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
      _transportsUnary, _routesUnary, provenanceUnary, _nameUnary, _indexWindowsModulus,
      _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, _namePkg⟩
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tailUnary indexTailRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have budgetUnary : UnaryHistory sealBudgetRead :=
    unary_cont_closed tailReadUnary sealReadUnary readSealBudget
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed budgetUnary provenanceUnary budgetProvenanceCompletion
  have replacementUnary : UnaryHistory replacementRead :=
    unary_transport completionUnary (hsame_symm replacementCompletion)
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro replacementRead (And.intro packetWitness (hsame_refl replacementRead))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      have completionRow : hsame completionRead row :=
        hsame_trans (hsame_symm replacementCompletion) (hsame_symm source.right)
      exact
        ⟨cont_result_hsame_transport budgetProvenanceCompletion completionRow, source.right⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport replacementUnary (hsame_symm source.right), replacementPkg,
          (fun hostReturn =>
            cont_mutual_extension_right_tail_absurd.left readSealBudget hostReturn),
          (fun hostReturn =>
            cont_mutual_extension_right_tail_absurd.right readSealBudget hostReturn)⟩
  }

end BEDC.Derived.UniformCauchyCriterionUp
