import BEDC.Derived.CauchyCompletionReflectorUp

namespace BEDC.Derived.CauchyCompletionReflectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionReflectorPacket_obligation_triple [AskSetup] [PackageSetup]
    {source completionObject unit counit idempotent extension reflection transport
      componentTransport replay provenance localName exported extensionRead reflectionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionReflectorPacket source completionObject unit counit idempotent extension
        reflection transport componentTransport replay provenance localName exported bundle pkg →
      Cont unit extension extensionRead →
        Cont extension reflection reflectionRead →
          PkgSig bundle reflectionRead pkg →
            UnaryHistory unit ∧ UnaryHistory counit ∧ UnaryHistory idempotent ∧
              UnaryHistory extension ∧ UnaryHistory reflection ∧ UnaryHistory extensionRead ∧
                UnaryHistory reflectionRead ∧ Cont source unit completionObject ∧
                  Cont completionObject counit transport ∧ Cont idempotent extension reflection ∧
                    Cont unit extension extensionRead ∧
                      Cont extension reflection reflectionRead ∧
                        PkgSig bundle exported pkg ∧ PkgSig bundle reflectionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet unitExtensionRead extensionReflectionRead reflectionReadPkg
  obtain ⟨_sourceUnary, _completionUnary, unitUnary, counitUnary, idempotentUnary,
    extensionUnary, reflectionUnary, _transportUnary, _componentTransportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _exportedUnary, sourceUnitCompletion,
    completionCounitTransport, idempotentExtensionReflection, _componentReplayProvenance,
    _provenanceLocalExported, exportedPkg⟩ := packet
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed unitUnary extensionUnary unitExtensionRead
  have reflectionReadUnary : UnaryHistory reflectionRead :=
    unary_cont_closed extensionUnary reflectionUnary extensionReflectionRead
  exact
    ⟨unitUnary, counitUnary, idempotentUnary, extensionUnary, reflectionUnary,
      extensionReadUnary, reflectionReadUnary, sourceUnitCompletion,
      completionCounitTransport, idempotentExtensionReflection, unitExtensionRead,
      extensionReflectionRead, exportedPkg, reflectionReadPkg⟩

end BEDC.Derived.CauchyCompletionReflectorUp
