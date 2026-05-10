import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TannakaKreinUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TannakaKreinFiberFunctorCarrier [AskSetup] [PackageSetup]
    (lieGroup monoidalCat fiberFunctor repObject tensorUnit tensorProduct reconstruction
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory lieGroup ∧ UnaryHistory monoidalCat ∧ UnaryHistory fiberFunctor ∧
    UnaryHistory repObject ∧ UnaryHistory tensorUnit ∧ UnaryHistory tensorProduct ∧
      Cont lieGroup monoidalCat reconstruction ∧ Cont reconstruction fiberFunctor endpoint ∧
        PkgSig bundle endpoint pkg

theorem TannakaKreinFiberFunctorCarrier_reconstruction_ledger_exactness
    [AskSetup] [PackageSetup]
    {lieGroup monoidalCat fiberFunctor repObject tensorUnit tensorProduct reconstruction
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TannakaKreinFiberFunctorCarrier lieGroup monoidalCat fiberFunctor repObject tensorUnit
        tensorProduct reconstruction endpoint bundle pkg ->
      UnaryHistory reconstruction ∧ UnaryHistory endpoint ∧
        hsame reconstruction (append lieGroup monoidalCat) ∧
          hsame endpoint (append reconstruction fiberFunctor) ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  have reconstructionUnary : UnaryHistory reconstruction :=
    unary_cont_closed carrier.left carrier.right.left
      carrier.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed reconstructionUnary carrier.right.right.left
      carrier.right.right.right.right.right.right.right.left
  exact
    ⟨reconstructionUnary, endpointUnary, carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.TannakaKreinUp
