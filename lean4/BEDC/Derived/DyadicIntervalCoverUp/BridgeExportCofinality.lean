import BEDC.Derived.DyadicIntervalCoverUp

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverBridgeExportCofinality [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N bridgeRead cofinalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory L ∧ UnaryHistory U ∧ UnaryHistory M ∧ UnaryHistory R ∧
      UnaryHistory V ∧ UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory A ∧
        UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
          Cont M R bridgeRead ∧ PkgSig bundle P pkg) ->
      Cont bridgeRead A cofinalRead ->
        PkgSig bundle cofinalRead pkg ->
          UnaryHistory bridgeRead ∧ UnaryHistory cofinalRead ∧
            Cont M R bridgeRead ∧ Cont bridgeRead A cofinalRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle cofinalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro surface cofinalRoute cofinalPkg
  have mUnary : UnaryHistory M := surface.right.right.left
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have bridgeRoute : Cont M R bridgeRead :=
    surface.right.right.right.right.right.right.right.right.right.right.right.right.left
  have carrierPkg : PkgSig bundle P pkg :=
    surface.right.right.right.right.right.right.right.right.right.right.right.right.right
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed mUnary rUnary bridgeRoute
  have aUnary : UnaryHistory A :=
    surface.right.right.right.right.right.right.right.left
  have cofinalUnary : UnaryHistory cofinalRead :=
    unary_cont_closed bridgeUnary aUnary cofinalRoute
  exact ⟨bridgeUnary, cofinalUnary, bridgeRoute, cofinalRoute, carrierPkg, cofinalPkg⟩

end BEDC.Derived.DyadicIntervalCoverUp
