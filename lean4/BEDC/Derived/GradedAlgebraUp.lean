import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.GradedAlgebraUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def GradedAlgebraPacket [AskSetup] [PackageSetup]
    (ring degree component multiplication action provenance product moduleRead endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory ring ∧ UnaryHistory degree ∧ UnaryHistory component ∧
    UnaryHistory multiplication ∧ UnaryHistory action ∧ UnaryHistory provenance ∧
      UnaryHistory product ∧ UnaryHistory moduleRead ∧ UnaryHistory endpoint ∧
        Cont ring degree component ∧ Cont component multiplication product ∧
          Cont product action moduleRead ∧ Cont moduleRead provenance endpoint ∧
            PkgSig bundle endpoint pkg

theorem GradedAlgebraPacket_component_stability [AskSetup] [PackageSetup]
    {ring degree component multiplication action provenance product moduleRead endpoint
      ring' degree' component' multiplication' action' provenance' product' moduleRead'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GradedAlgebraPacket ring degree component multiplication action provenance product
        moduleRead endpoint bundle pkg ->
      hsame ring ring' -> hsame degree degree' -> hsame component component' ->
        hsame multiplication multiplication' -> hsame action action' ->
          hsame provenance provenance' -> Cont ring' degree' component' ->
            Cont component' multiplication' product' ->
              Cont product' action' moduleRead' ->
                Cont moduleRead' provenance' endpoint' ->
                  PkgSig bundle endpoint' pkg ->
                    GradedAlgebraPacket ring' degree' component' multiplication' action'
                        provenance' product' moduleRead' endpoint' bundle pkg ∧
                      hsame product product' ∧ hsame moduleRead moduleRead' ∧
                        hsame endpoint endpoint' := by
  intro packet sameRing sameDegree sameComponent sameMultiplication sameAction sameProvenance
    componentCont' productCont' moduleCont' endpointCont' pkgSig'
  have ringUnary' : UnaryHistory ring' :=
    unary_transport packet.left sameRing
  have degreeUnary' : UnaryHistory degree' :=
    unary_transport packet.right.left sameDegree
  have componentUnary' : UnaryHistory component' :=
    unary_transport packet.right.right.left sameComponent
  have multiplicationUnary' : UnaryHistory multiplication' :=
    unary_transport packet.right.right.right.left sameMultiplication
  have actionUnary' : UnaryHistory action' :=
    unary_transport packet.right.right.right.right.left sameAction
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport packet.right.right.right.right.right.left sameProvenance
  have sameProduct : hsame product product' :=
    cont_respects_hsame sameComponent sameMultiplication
      packet.right.right.right.right.right.right.right.right.right.right.left productCont'
  have productUnary' : UnaryHistory product' :=
    unary_transport packet.right.right.right.right.right.right.left sameProduct
  have sameModuleRead : hsame moduleRead moduleRead' :=
    cont_respects_hsame sameProduct sameAction
      packet.right.right.right.right.right.right.right.right.right.right.right.left moduleCont'
  have moduleReadUnary' : UnaryHistory moduleRead' :=
    unary_transport packet.right.right.right.right.right.right.right.left sameModuleRead
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameModuleRead sameProvenance
      packet.right.right.right.right.right.right.right.right.right.right.right.right.left
      endpointCont'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport packet.right.right.right.right.right.right.right.right.left sameEndpoint
  exact And.intro
    (And.intro ringUnary'
      (And.intro degreeUnary'
        (And.intro componentUnary'
          (And.intro multiplicationUnary'
            (And.intro actionUnary'
              (And.intro provenanceUnary'
                (And.intro productUnary'
                  (And.intro moduleReadUnary'
                    (And.intro endpointUnary'
                      (And.intro componentCont'
                        (And.intro productCont'
                          (And.intro moduleCont'
                            (And.intro endpointCont' pkgSig')))))))))))))
    (And.intro sameProduct (And.intro sameModuleRead sameEndpoint))

end BEDC.Derived.GradedAlgebraUp
