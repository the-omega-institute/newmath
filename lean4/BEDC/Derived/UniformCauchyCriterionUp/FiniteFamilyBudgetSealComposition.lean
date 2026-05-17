import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_finite_family_budget_seal_composition [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name endpointRead
      streamExit regseqSeal realWindowCompletion budgetSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index name endpointRead ->
        Cont windows tail streamExit ->
          Cont tail sealRow regseqSeal ->
            Cont endpointRead regseqSeal realWindowCompletion ->
              Cont streamExit realWindowCompletion budgetSeal ->
                PkgSig bundle budgetSeal pkg ->
                  UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                    UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                      UnaryHistory endpointRead ∧ UnaryHistory streamExit ∧
                        UnaryHistory regseqSeal ∧ UnaryHistory realWindowCompletion ∧
                          UnaryHistory budgetSeal ∧ Cont index windows modulus ∧
                            Cont modulus tolerance tail ∧ Cont index name endpointRead ∧
                              Cont windows tail streamExit ∧ Cont tail sealRow regseqSeal ∧
                                Cont endpointRead regseqSeal realWindowCompletion ∧
                                  Cont streamExit realWindowCompletion budgetSeal ∧
                                    PkgSig bundle name pkg ∧ PkgSig bundle budgetSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexNameEndpoint windowsTailStream tailSealRegseq endpointRegseqRealWindow
    streamRealWindowBudget budgetPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed indexUnary nameUnary indexNameEndpoint
  have streamUnary : UnaryHistory streamExit :=
    unary_cont_closed windowsUnary tailUnary windowsTailStream
  have regseqUnary : UnaryHistory regseqSeal :=
    unary_cont_closed tailUnary sealRowUnary tailSealRegseq
  have realWindowUnary : UnaryHistory realWindowCompletion :=
    unary_cont_closed endpointUnary regseqUnary endpointRegseqRealWindow
  have budgetUnary : UnaryHistory budgetSeal :=
    unary_cont_closed streamUnary realWindowUnary streamRealWindowBudget
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      endpointUnary, streamUnary, regseqUnary, realWindowUnary, budgetUnary,
      indexWindowsModulus, modulusToleranceTail, indexNameEndpoint, windowsTailStream,
      tailSealRegseq, endpointRegseqRealWindow, streamRealWindowBudget, namePkg,
      budgetPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
