import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyCompletionReflectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyCompletionReflectorPacket [AskSetup] [PackageSetup]
    (source completionObject unit counit idempotent extension reflection transport
      componentTransport replay provenance localName exported : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  UnaryHistory source ∧ UnaryHistory completionObject ∧ UnaryHistory unit ∧
    UnaryHistory counit ∧ UnaryHistory idempotent ∧ UnaryHistory extension ∧
      UnaryHistory reflection ∧ UnaryHistory transport ∧ UnaryHistory componentTransport ∧
        UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
          UnaryHistory exported ∧ Cont source unit completionObject ∧
            Cont completionObject counit transport ∧ Cont idempotent extension reflection ∧
              Cont componentTransport replay provenance ∧ Cont provenance localName exported ∧
                PkgSig bundle exported pkg

theorem CauchyCompletionReflectorPacket_semantic_name_certificate
    [AskSetup] [PackageSetup]
    {source completionObject unit counit idempotent extension reflection transport
      componentTransport replay provenance localName exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionReflectorPacket source completionObject unit counit idempotent
        extension reflection transport componentTransport replay provenance localName exported
        bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          CauchyCompletionReflectorPacket source completionObject unit counit idempotent
              extension reflection transport componentTransport replay provenance localName exported
              bundle pkg ∧
            hsame row localName)
        (fun row : BHist =>
          CauchyCompletionReflectorPacket source completionObject unit counit idempotent
              extension reflection transport componentTransport replay provenance localName exported
              bundle pkg ∧
            hsame row localName)
        (fun row : BHist =>
          CauchyCompletionReflectorPacket source completionObject unit counit idempotent
              extension reflection transport componentTransport replay provenance localName exported
              bundle pkg ∧
            hsame row localName)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro localName ⟨packet, hsame_refl localName⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem CauchyCompletionReflectorPacket_unit_counit_route [AskSetup] [PackageSetup]
    {source completionObject unit counit idempotent extension reflection transport
      componentTransport replay provenance localName exported returnRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionReflectorPacket source completionObject unit counit idempotent extension
        reflection transport componentTransport replay provenance localName exported bundle pkg →
      Cont transport provenance returnRead →
        PkgSig bundle returnRead pkg →
          UnaryHistory source ∧ UnaryHistory unit ∧ UnaryHistory completionObject ∧
            UnaryHistory counit ∧ UnaryHistory transport ∧ UnaryHistory returnRead ∧
              Cont source unit completionObject ∧ Cont completionObject counit transport ∧
                Cont transport provenance returnRead ∧ PkgSig bundle exported pkg ∧
                  PkgSig bundle returnRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle Pkg PkgSig
  intro packet returnCont returnPkg
  rcases packet with
    ⟨sourceUnary, completionUnary, unitUnary, counitUnary, _idempotentUnary,
      _extensionUnary, _reflectionUnary, transportUnary, _componentTransportUnary,
      _replayUnary, provenanceUnary, _localNameUnary, _exportedUnary, sourceUnitCont,
      completionCounitCont, _idempotentExtensionCont, _componentReplayCont,
      _provenanceNameCont, exportedPkg⟩
  have returnUnary : UnaryHistory returnRead :=
    unary_cont_closed transportUnary provenanceUnary returnCont
  exact ⟨sourceUnary, unitUnary, completionUnary, counitUnary, transportUnary, returnUnary,
    sourceUnitCont, completionCounitCont, returnCont, exportedPkg, returnPkg⟩

theorem CauchyCompletionReflectorPacket_idempotent_extension_obligation
    [AskSetup] [PackageSetup]
    {source completionObject unit counit idempotent extension reflection transport
      componentTransport replay provenance localName exported reflectedRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionReflectorPacket source completionObject unit counit idempotent extension
        reflection transport componentTransport replay provenance localName exported bundle pkg →
      Cont reflection transport reflectedRoute →
        PkgSig bundle reflectedRoute pkg →
          UnaryHistory idempotent ∧ UnaryHistory extension ∧ UnaryHistory reflection ∧
            UnaryHistory transport ∧ UnaryHistory reflectedRoute ∧
              Cont idempotent extension reflection ∧
                Cont reflection transport reflectedRoute ∧ PkgSig bundle exported pkg ∧
                  PkgSig bundle reflectedRoute pkg := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle Pkg PkgSig
  intro packet reflectedCont reflectedPkg
  rcases packet with
    ⟨_sourceUnary, _completionUnary, _unitUnary, _counitUnary, idempotentUnary,
      extensionUnary, reflectionUnary, transportUnary, _componentTransportUnary,
      _replayUnary, _provenanceUnary, _localNameUnary, _exportedUnary, _sourceUnitCont,
      _completionCounitCont, idempotentExtensionCont, _componentReplayCont,
      _provenanceNameCont, exportedPkg⟩
  have reflectedUnary : UnaryHistory reflectedRoute :=
    unary_cont_closed reflectionUnary transportUnary reflectedCont
  exact ⟨idempotentUnary, extensionUnary, reflectionUnary, transportUnary, reflectedUnary,
    idempotentExtensionCont, reflectedCont, exportedPkg, reflectedPkg⟩

end BEDC.Derived.CauchyCompletionReflectorUp
