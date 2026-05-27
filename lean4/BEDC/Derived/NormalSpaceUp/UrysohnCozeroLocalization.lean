import BEDC.Derived.NormalSpaceUp.TasteGate

namespace BEDC.Derived.NormalSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormalSpacePacket_urysohn_cozero_localization [AskSetup] [PackageSetup]
    {topology closedLeft closedRight disjoint openLeft openRight transport replay provenance
      localName exported cozeroRead urysohnRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormalSpacePacket topology closedLeft closedRight disjoint openLeft openRight transport
        replay provenance localName exported bundle pkg →
      Cont openLeft openRight cozeroRead →
        Cont disjoint transport urysohnRead →
          PkgSig bundle cozeroRead pkg →
            PkgSig bundle urysohnRead pkg →
              UnaryHistory topology ∧ UnaryHistory closedLeft ∧ UnaryHistory closedRight ∧
                UnaryHistory disjoint ∧ UnaryHistory openLeft ∧ UnaryHistory openRight ∧
                  UnaryHistory cozeroRead ∧ UnaryHistory urysohnRead ∧
                    Cont openLeft openRight cozeroRead ∧ Cont disjoint transport urysohnRead ∧
                      PkgSig bundle localName pkg ∧ PkgSig bundle cozeroRead pkg ∧
                        PkgSig bundle urysohnRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet cozeroRoute urysohnRoute cozeroPkg urysohnPkg
  have cozeroUnary : UnaryHistory cozeroRead :=
    unary_cont_closed packet.right.right.right.right.left
      packet.right.right.right.right.right.left cozeroRoute
  have urysohnUnary : UnaryHistory urysohnRead :=
    unary_cont_closed packet.right.right.right.left
      packet.right.right.right.right.right.right.left urysohnRoute
  exact
    ⟨packet.left,
      packet.right.left,
      packet.right.right.left,
      packet.right.right.right.left,
      packet.right.right.right.right.left,
      packet.right.right.right.right.right.left,
      cozeroUnary,
      urysohnUnary,
      cozeroRoute,
      urysohnRoute,
      packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right,
      cozeroPkg,
      urysohnPkg⟩

end BEDC.Derived.NormalSpaceUp
