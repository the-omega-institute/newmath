import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.StackUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def StackBHistCarrier [AskSetup] [PackageSetup]
    (site groupoid objects arrows restriction descent representability provenance endpoint :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory site ∧ UnaryHistory groupoid ∧ UnaryHistory arrows ∧ UnaryHistory descent ∧
    UnaryHistory provenance ∧ Cont site groupoid objects ∧ Cont objects arrows restriction ∧
      Cont restriction descent representability ∧ Cont representability provenance endpoint ∧
        PkgSig bundle endpoint pkg

theorem StackBHistCarrier_descent_obligation [AskSetup] [PackageSetup]
    {site groupoid objects arrows restriction descent representability provenance endpoint descent'
      representability' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StackBHistCarrier site groupoid objects arrows restriction descent representability provenance
        endpoint bundle pkg ->
      hsame descent descent' ->
      Cont restriction descent' representability' ->
      Cont representability' provenance endpoint' ->
      PkgSig bundle endpoint' pkg ->
      StackBHistCarrier site groupoid objects arrows restriction descent' representability'
          provenance endpoint' bundle pkg ∧
        hsame representability representability' ∧ hsame endpoint endpoint' := by
  intro carrier sameDescent representabilityCont' endpointCont' pkgSig'
  have descentUnary' : UnaryHistory descent' :=
    unary_transport carrier.right.right.right.left sameDescent
  have sameRepresentability : hsame representability representability' :=
    cont_respects_hsame (hsame_refl restriction) sameDescent
      carrier.right.right.right.right.right.right.right.left representabilityCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameRepresentability (hsame_refl provenance)
      carrier.right.right.right.right.right.right.right.right.left endpointCont'
  exact
    ⟨⟨carrier.left,
        carrier.right.left,
        carrier.right.right.left,
        descentUnary',
        carrier.right.right.right.right.left,
        carrier.right.right.right.right.right.left,
        carrier.right.right.right.right.right.right.left,
        representabilityCont',
        endpointCont',
        pkgSig'⟩,
      sameRepresentability,
      sameEndpoint⟩

end BEDC.Derived.StackUp
