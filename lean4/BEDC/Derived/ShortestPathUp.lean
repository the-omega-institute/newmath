import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ShortestPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ShortestPathWeightedGraphCarrier [AskSetup] [PackageSetup]
    (vertices edges weights source target path incidence weightedPath endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory vertices ∧ UnaryHistory edges ∧ UnaryHistory weights ∧
    UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory path ∧
      Cont vertices edges incidence ∧ Cont incidence weights weightedPath ∧
        Cont weightedPath path endpoint ∧ PkgSig bundle endpoint pkg

theorem ShortestPathWeightedGraphCarrier_visible_path_ledger [AskSetup] [PackageSetup]
    {vertices edges weights source target path incidence weightedPath endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ShortestPathWeightedGraphCarrier vertices edges weights source target path incidence
        weightedPath endpoint bundle pkg ->
      UnaryHistory incidence ∧ UnaryHistory weightedPath ∧ UnaryHistory endpoint ∧
        hsame incidence (append vertices edges) ∧ hsame weightedPath (append incidence weights) ∧
          hsame endpoint (append weightedPath path) ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  have incidenceUnary : UnaryHistory incidence :=
    unary_cont_closed carrier.left carrier.right.left
      carrier.right.right.right.right.right.right.left
  have weightedPathUnary : UnaryHistory weightedPath :=
    unary_cont_closed incidenceUnary carrier.right.right.left
      carrier.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed weightedPathUnary carrier.right.right.right.right.right.left
      carrier.right.right.right.right.right.right.right.right.left
  exact
    ⟨incidenceUnary, weightedPathUnary, endpointUnary,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.ShortestPathUp
