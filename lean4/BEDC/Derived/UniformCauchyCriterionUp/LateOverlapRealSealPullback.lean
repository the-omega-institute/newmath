import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_late_overlap_real_seal_pullback [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name sharedSchedule
      overlapBudget regseqConsumer realSealPullback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont modulus tail sharedSchedule ->
        Cont sharedSchedule tolerance overlapBudget ->
          Cont overlapBudget tail regseqConsumer ->
            Cont regseqConsumer sealRow realSealPullback ->
              PkgSig bundle realSealPullback pkg ->
                UnaryHistory sharedSchedule ∧ UnaryHistory overlapBudget ∧
                  UnaryHistory regseqConsumer ∧ UnaryHistory realSealPullback ∧
                    Cont modulus tail sharedSchedule ∧
                      Cont sharedSchedule tolerance overlapBudget ∧
                        Cont overlapBudget tail regseqConsumer ∧
                          Cont regseqConsumer sealRow realSealPullback ∧
                            PkgSig bundle name pkg ∧ PkgSig bundle realSealPullback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet modulusTailSchedule scheduleToleranceBudget budgetTailRegseq regseqSealPullback
    pullbackPkg
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
  have pullbackUnary : UnaryHistory realSealPullback :=
    unary_cont_closed regseqUnary sealRowUnary regseqSealPullback
  exact
    ⟨scheduleUnary, budgetUnary, regseqUnary, pullbackUnary, modulusTailSchedule,
      scheduleToleranceBudget, budgetTailRegseq, regseqSealPullback, namePkg, pullbackPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
