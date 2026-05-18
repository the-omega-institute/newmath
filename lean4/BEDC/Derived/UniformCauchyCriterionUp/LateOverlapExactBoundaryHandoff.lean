import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_late_overlap_exact_boundary_handoff [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name sharedSchedule
      overlapBudget regseqConsumer exactBoundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont modulus tail sharedSchedule ->
        Cont sharedSchedule tolerance overlapBudget ->
          Cont overlapBudget tail regseqConsumer ->
            Cont regseqConsumer sealRow exactBoundaryRead ->
              PkgSig bundle regseqConsumer pkg ->
                PkgSig bundle exactBoundaryRead pkg ->
                  SemanticNameCert
                    (fun row : BHist =>
                      UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow
                        transports routes provenance name bundle pkg ∧
                          hsame row exactBoundaryRead)
                    (fun row : BHist =>
                      Cont modulus tail sharedSchedule ∧
                        Cont sharedSchedule tolerance overlapBudget ∧
                          Cont overlapBudget tail regseqConsumer ∧
                            Cont regseqConsumer sealRow row)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle regseqConsumer pkg ∧
                        PkgSig bundle exactBoundaryRead pkg)
                    hsame ∧
                    UnaryHistory regseqConsumer ∧ UnaryHistory exactBoundaryRead ∧
                      Cont overlapBudget tail regseqConsumer ∧
                        Cont regseqConsumer sealRow exactBoundaryRead ∧
                          PkgSig bundle name pkg ∧ PkgSig bundle regseqConsumer pkg ∧
                            PkgSig bundle exactBoundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet modulusTailSchedule scheduleToleranceBudget budgetTailRegseq
    regseqSealExact regseqPkg exactPkg
  have packetWitness :
      UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg := packet
  obtain ⟨_indexUnary, _windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
      packet
  have scheduleUnary : UnaryHistory sharedSchedule :=
    unary_cont_closed modulusUnary tailUnary modulusTailSchedule
  have budgetUnary : UnaryHistory overlapBudget :=
    unary_cont_closed scheduleUnary toleranceUnary scheduleToleranceBudget
  have regseqUnary : UnaryHistory regseqConsumer :=
    unary_cont_closed budgetUnary tailUnary budgetTailRegseq
  have exactUnary : UnaryHistory exactBoundaryRead :=
    unary_cont_closed regseqUnary sealRowUnary regseqSealExact
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports
            routes provenance name bundle pkg ∧ hsame row exactBoundaryRead)
        (fun row : BHist =>
          Cont modulus tail sharedSchedule ∧ Cont sharedSchedule tolerance overlapBudget ∧
            Cont overlapBudget tail regseqConsumer ∧ Cont regseqConsumer sealRow row)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle regseqConsumer pkg ∧
            PkgSig bundle exactBoundaryRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro exactBoundaryRead
        (And.intro packetWitness (hsame_refl exactBoundaryRead))
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
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact
        ⟨modulusTailSchedule, scheduleToleranceBudget, budgetTailRegseq,
          cont_result_hsame_transport regseqSealExact (hsame_symm source.right)⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport exactUnary (hsame_symm source.right), regseqPkg, exactPkg⟩
  }
  exact
    ⟨cert, regseqUnary, exactUnary, budgetTailRegseq, regseqSealExact, namePkg, regseqPkg,
      exactPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
