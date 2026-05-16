import BEDC.Derived.KernelMorphismUp

namespace BEDC.Derived.KernelMorphismUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KernelMorphismCarrier_composition_standard_reflection_compatibility
    [AskSetup] [PackageSetup]
    {source middle target graphLeft graphRight edgeLeft edgeRight liftLeft liftRight
      transportLeft routesLeft provenanceLeft certLeft transportRight routesRight
      provenanceRight certRight compositeGraph compositeEdge bridgeLeft bridgeRight
      compositeBridge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelMorphismCarrier source middle graphLeft edgeLeft liftLeft transportLeft routesLeft
        provenanceLeft certLeft bundle pkg →
      KernelMorphismCarrier middle target graphRight edgeRight liftRight transportRight
          routesRight provenanceRight certRight bundle pkg →
        Cont graphLeft graphRight compositeGraph →
          Cont edgeLeft edgeRight compositeEdge →
            Cont source middle bridgeLeft →
              Cont middle target bridgeRight →
                Cont bridgeLeft bridgeRight compositeBridge →
                  PkgSig bundle compositeBridge pkg →
                    SemanticNameCert
                      (fun row : BHist =>
                        hsame row compositeBridge ∧ UnaryHistory row ∧
                          PkgSig bundle row pkg)
                      (fun row : BHist =>
                        Cont graphLeft graphRight compositeGraph ∧
                          Cont edgeLeft edgeRight compositeEdge ∧
                            Cont bridgeLeft bridgeRight compositeBridge ∧
                              hsame row compositeBridge)
                      (fun row : BHist =>
                        PkgSig bundle row pkg ∧ PkgSig bundle provenanceLeft pkg ∧
                          PkgSig bundle provenanceRight pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont PkgSig
  intro leftCarrier rightCarrier graphComposite edgeComposite leftBridge rightBridge
    bridgeComposite compositePkg
  obtain ⟨sourceUnary, middleUnary, graphLeftUnary, edgeLeftUnary, _liftLeftUnary,
    _transportLeftUnary, _routesLeftUnary, _provenanceLeftUnary, _certLeftUnary,
    _sourceGraphLeftEdge, _edgeLiftLeftMiddle, _transportLeftRoutesProvenance,
    provenanceLeftPkg, _certLeftPkg⟩ := leftCarrier
  obtain ⟨_middleUnaryRight, targetUnary, graphRightUnary, edgeRightUnary,
    _liftRightUnary, _transportRightUnary, _routesRightUnary, _provenanceRightUnary,
    _certRightUnary, _middleGraphRightEdge, _edgeLiftRightTarget,
    _transportRightRoutesProvenance, provenanceRightPkg, _certRightPkg⟩ := rightCarrier
  have bridgeLeftUnary : UnaryHistory bridgeLeft :=
    unary_cont_closed sourceUnary middleUnary leftBridge
  have bridgeRightUnary : UnaryHistory bridgeRight :=
    unary_cont_closed middleUnary targetUnary rightBridge
  have compositeBridgeUnary : UnaryHistory compositeBridge :=
    unary_cont_closed bridgeLeftUnary bridgeRightUnary bridgeComposite
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro compositeBridge
          ⟨hsame_refl compositeBridge, compositeBridgeUnary, compositePkg⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same sourceRow
        cases same
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact ⟨graphComposite, edgeComposite, bridgeComposite, sourceRow.left⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, provenanceLeftPkg, provenanceRightPkg⟩
  }

end BEDC.Derived.KernelMorphismUp
