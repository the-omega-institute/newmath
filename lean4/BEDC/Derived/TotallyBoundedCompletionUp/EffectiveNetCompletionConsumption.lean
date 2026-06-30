import BEDC.Derived.TotallyBoundedCompletionUp

namespace BEDC.Derived.TotallyBoundedCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TotallyBoundedCompletionCarrier_effective_net_completion_consumption
    [AskSetup] [PackageSetup]
    {source totalBounded netLedger filter embedding completion separated extension transport
      provenance localName selectorRead completionRead extensionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source totalBounded netLedger filter embedding completion
        separated extension transport provenance localName bundle pkg ->
      Cont totalBounded netLedger selectorRead ->
        Cont filter embedding completionRead ->
          Cont completionRead separated extensionRead ->
            PkgSig bundle extensionRead pkg ->
              UnaryHistory selectorRead ∧ UnaryHistory completionRead ∧
                UnaryHistory extensionRead ∧ Cont totalBounded netLedger selectorRead ∧
                  Cont filter embedding completionRead ∧
                    Cont completionRead separated extensionRead ∧
                      PkgSig bundle extensionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier selectorRoute completionRoute extensionRoute extensionPkg
  obtain
    ⟨sourceUnary, totalBoundedUnary, filterUnary, completionUnary, _extensionUnary,
      _transportUnary, totalBoundedNetLedger, netLedgerFilterEmbedding,
      embeddingCompletionSeparated, _separatedExtensionProvenance,
      _transportProvenanceLocalName, _provenancePkg, _localNamePkg⟩ := carrier
  have netLedgerUnary : UnaryHistory netLedger :=
    unary_cont_closed sourceUnary totalBoundedUnary totalBoundedNetLedger
  have embeddingUnary : UnaryHistory embedding :=
    unary_cont_closed netLedgerUnary filterUnary netLedgerFilterEmbedding
  have separatedUnary : UnaryHistory separated :=
    unary_cont_closed embeddingUnary completionUnary embeddingCompletionSeparated
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed totalBoundedUnary netLedgerUnary selectorRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed filterUnary embeddingUnary completionRoute
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed completionReadUnary separatedUnary extensionRoute
  exact
    ⟨selectorReadUnary, completionReadUnary, extensionReadUnary, selectorRoute,
      completionRoute, extensionRoute, extensionPkg⟩

end BEDC.Derived.TotallyBoundedCompletionUp
