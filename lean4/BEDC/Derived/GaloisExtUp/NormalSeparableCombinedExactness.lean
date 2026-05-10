import BEDC.Derived.GaloisExtUp

namespace BEDC.Derived.GaloisExtUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem GaloisExtSourcePacket_normal_separable_combined_exactness [AskSetup] [PackageSetup]
    {fieldExt polynomial generator minimal simpleRoot sepProvenance separable normality
      separability classifier provenance endpoint combined : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisExtSourcePacket fieldExt polynomial generator minimal simpleRoot sepProvenance separable
        normality separability classifier provenance endpoint bundle pkg ->
      Cont (append normality separability) endpoint combined ->
        UnaryHistory combined ∧
          hsame combined (append (append normality separability) (append provenance classifier)) ∧
            hsame classifier (append normality separability) ∧ PkgSig bundle endpoint pkg := by
  intro packet combinedCont
  have dependencyRows :=
    GaloisExtSourcePacket_dependency_exactness_ledger packet
  have normalSeparableUnary : UnaryHistory (append normality separability) :=
    unary_append_closed packet.right.left packet.right.right.left
  have combinedUnary : UnaryHistory combined :=
    unary_cont_closed normalSeparableUnary dependencyRows.right.right.left combinedCont
  have endpointReadback : hsame endpoint (append provenance classifier) :=
    dependencyRows.right.right.right.right.right.left
  have combinedReadback :
      hsame combined (append (append normality separability) (append provenance classifier)) :=
    hsame_trans combinedCont
      (congrArg (fun h : BHist => append (append normality separability) h) endpointReadback)
  exact And.intro combinedUnary
    (And.intro combinedReadback
      (And.intro dependencyRows.right.right.right.right.left
        dependencyRows.right.right.right.right.right.right))

end BEDC.Derived.GaloisExtUp
