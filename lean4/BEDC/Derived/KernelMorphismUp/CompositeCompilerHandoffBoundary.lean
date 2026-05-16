import BEDC.Derived.KernelMorphismUp

namespace BEDC.Derived.KernelMorphismUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KernelMorphismCarrier_composite_compiler_handoff_boundary
    [AskSetup] [PackageSetup]
    {source middle target graphLeft graphRight edgeLeft edgeRight liftLeft liftRight
      transportLeft routesLeft provenanceLeft certLeft transportRight routesRight
      provenanceRight certRight compositeGraph compositeEdge compilerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelMorphismCarrier source middle graphLeft edgeLeft liftLeft transportLeft routesLeft
        provenanceLeft certLeft bundle pkg →
      KernelMorphismCarrier middle target graphRight edgeRight liftRight transportRight
          routesRight provenanceRight certRight bundle pkg →
        Cont graphLeft graphRight compositeGraph →
          Cont edgeLeft edgeRight compositeEdge →
            Cont source target compilerRead →
              PkgSig bundle compilerRead pkg →
                UnaryHistory source ∧ UnaryHistory middle ∧ UnaryHistory target ∧
                  UnaryHistory compositeGraph ∧ UnaryHistory compositeEdge ∧
                    UnaryHistory compilerRead ∧ Cont graphLeft graphRight compositeGraph ∧
                      Cont edgeLeft edgeRight compositeEdge ∧ Cont source target compilerRead ∧
                        PkgSig bundle provenanceLeft pkg ∧
                          PkgSig bundle provenanceRight pkg ∧
                            PkgSig bundle compilerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro leftCarrier rightCarrier graphComposite edgeComposite compilerRoute compilerPkg
  obtain ⟨sourceUnary, middleUnary, graphLeftUnary, edgeLeftUnary, _liftLeftUnary,
    _transportLeftUnary, _routesLeftUnary, _provenanceLeftUnary, _certLeftUnary,
    _sourceGraphLeftEdge, _edgeLiftLeftMiddle, _transportLeftRoutesProvenance,
    provenanceLeftPkg, _certLeftPkg⟩ := leftCarrier
  obtain ⟨_middleUnaryRight, targetUnary, graphRightUnary, edgeRightUnary,
    _liftRightUnary, _transportRightUnary, _routesRightUnary, _provenanceRightUnary,
    _certRightUnary, _middleGraphRightEdge, _edgeLiftRightTarget,
    _transportRightRoutesProvenance, provenanceRightPkg, _certRightPkg⟩ := rightCarrier
  have compositeGraphUnary : UnaryHistory compositeGraph :=
    unary_cont_closed graphLeftUnary graphRightUnary graphComposite
  have compositeEdgeUnary : UnaryHistory compositeEdge :=
    unary_cont_closed edgeLeftUnary edgeRightUnary edgeComposite
  have compilerReadUnary : UnaryHistory compilerRead :=
    unary_cont_closed sourceUnary targetUnary compilerRoute
  exact
    ⟨sourceUnary, middleUnary, targetUnary, compositeGraphUnary, compositeEdgeUnary,
      compilerReadUnary, graphComposite, edgeComposite, compilerRoute, provenanceLeftPkg,
      provenanceRightPkg, compilerPkg⟩

end BEDC.Derived.KernelMorphismUp
