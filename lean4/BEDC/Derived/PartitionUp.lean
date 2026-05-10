import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.PartitionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PartitionBHistCarrier [AskSetup] [PackageSetup]
    (listRow partRows sumRow decreaseRows boundary route provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory listRow ∧ UnaryHistory partRows ∧ UnaryHistory sumRow ∧
    UnaryHistory decreaseRows ∧ UnaryHistory boundary ∧ Cont listRow sumRow route ∧
      Cont decreaseRows boundary provenance ∧ Cont route provenance endpoint ∧
        PkgSig bundle endpoint pkg

theorem PartitionBHistCarrier_young_boundary_package [AskSetup] [PackageSetup]
    {listRow partRows sumRow decreaseRows boundary route provenance endpoint routeBoundary
      packaged : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
        endpoint bundle pkg ->
      Cont route boundary routeBoundary ->
        Cont provenance routeBoundary packaged ->
          PkgSig bundle packaged pkg ->
            UnaryHistory routeBoundary ∧ UnaryHistory packaged ∧
              hsame routeBoundary (append route boundary) ∧
                hsame packaged (append provenance routeBoundary) := by
  intro carrier routeBoundaryCont packagedCont _packagedPkg
  have routeUnary : UnaryHistory route :=
    unary_cont_closed carrier.left carrier.right.right.left
      carrier.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed carrier.right.right.right.left carrier.right.right.right.right.left
      carrier.right.right.right.right.right.right.left
  have routeBoundaryUnary : UnaryHistory routeBoundary :=
    unary_cont_closed routeUnary carrier.right.right.right.right.left routeBoundaryCont
  have packagedUnary : UnaryHistory packaged :=
    unary_cont_closed provenanceUnary routeBoundaryUnary packagedCont
  exact
    ⟨routeBoundaryUnary,
      packagedUnary,
      routeBoundaryCont,
      packagedCont⟩

end BEDC.Derived.PartitionUp
