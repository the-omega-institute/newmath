import BEDC.Derived.KernelMorphismUp

namespace BEDC.Derived.KernelMorphismUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KernelMorphismCarrier_composition_surface [AskSetup] [PackageSetup]
    {source middle target graphLeft graphRight edgeLeft edgeRight liftLeft liftRight
      transportLeft routesLeft provenanceLeft certLeft transportRight routesRight provenanceRight
      certRight compositeGraph compositeEdge compositeLift compositeProvenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelMorphismCarrier source middle graphLeft edgeLeft liftLeft transportLeft routesLeft
        provenanceLeft certLeft bundle pkg →
      KernelMorphismCarrier middle target graphRight edgeRight liftRight transportRight routesRight
          provenanceRight certRight bundle pkg →
        Cont graphLeft graphRight compositeGraph →
          Cont edgeLeft edgeRight compositeEdge →
            Cont liftLeft liftRight compositeLift →
              Cont transportLeft routesRight compositeProvenance →
                PkgSig bundle compositeProvenance pkg →
                  UnaryHistory source ∧ UnaryHistory middle ∧ UnaryHistory target ∧
                    UnaryHistory compositeGraph ∧ UnaryHistory compositeEdge ∧
                      UnaryHistory compositeLift ∧ UnaryHistory compositeProvenance ∧
                        Cont source graphLeft edgeLeft ∧ Cont middle graphRight edgeRight ∧
                          Cont graphLeft graphRight compositeGraph ∧
                            Cont edgeLeft edgeRight compositeEdge ∧
                              Cont liftLeft liftRight compositeLift ∧
                                Cont transportLeft routesRight compositeProvenance ∧
                                  PkgSig bundle compositeProvenance pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg
  intro leftCarrier rightCarrier graphComposition edgeComposition liftComposition
    provenanceComposition compositePkg
  obtain ⟨sourceUnary, middleUnary, graphLeftUnary, edgeLeftUnary, liftLeftUnary,
    transportLeftUnary, _routesLeftUnary, _provenanceLeftUnary, _certLeftUnary,
    sourceGraphLeftEdge, _edgeLiftLeftMiddle, _transportLeftRoutesProvenance,
    _provenanceLeftPkg, _certLeftPkg⟩ := leftCarrier
  obtain ⟨_middleUnaryRight, targetUnary, graphRightUnary, edgeRightUnary, liftRightUnary,
    _transportRightUnary, routesRightUnary, _provenanceRightUnary, _certRightUnary,
    middleGraphRightEdge, _edgeLiftRightTarget, _transportRightRoutesProvenance,
    _provenanceRightPkg, _certRightPkg⟩ := rightCarrier
  have compositeGraphUnary : UnaryHistory compositeGraph :=
    unary_cont_closed graphLeftUnary graphRightUnary graphComposition
  have compositeEdgeUnary : UnaryHistory compositeEdge :=
    unary_cont_closed edgeLeftUnary edgeRightUnary edgeComposition
  have compositeLiftUnary : UnaryHistory compositeLift :=
    unary_cont_closed liftLeftUnary liftRightUnary liftComposition
  have compositeProvenanceUnary : UnaryHistory compositeProvenance :=
    unary_cont_closed transportLeftUnary routesRightUnary provenanceComposition
  exact
    ⟨sourceUnary, middleUnary, targetUnary, compositeGraphUnary, compositeEdgeUnary,
      compositeLiftUnary, compositeProvenanceUnary, sourceGraphLeftEdge, middleGraphRightEdge,
      graphComposition, edgeComposition, liftComposition, provenanceComposition, compositePkg⟩

end BEDC.Derived.KernelMorphismUp
