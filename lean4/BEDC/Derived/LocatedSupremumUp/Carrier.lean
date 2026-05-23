import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.LocatedSupremumUp.TasteGate

namespace BEDC.Derived.LocatedSupremumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedSupremumCarrier [AskSetup] [PackageSetup]
    (L U A W R E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist BMark
  UnaryHistory R ∧ UnaryHistory A ∧ Cont R A E ∧ hsame L U ∧ UnaryHistory W ∧
    Cont W R C ∧ hsame H (append C W) ∧ PkgSig bundle P pkg ∧ hsame N (append E H)

theorem LocatedSupremumCarrier_real_seal_boundary [AskSetup] [PackageSetup]
    {L U A W R E H C P N sealRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedSupremumCarrier L U A W R E H C P N bundle pkg ->
      Cont R E sealRead ->
        UnaryHistory sealRead /\ hsame E (append R A) /\ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist BMark
  intro carrier sealRoute
  have unaryR : UnaryHistory R := carrier.left
  have unaryA : UnaryHistory A := carrier.right.left
  have handoffRoute : Cont R A E := carrier.right.right.left
  have pkgSig : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.left
  have unaryE : UnaryHistory E := unary_cont_closed unaryR unaryA handoffRoute
  constructor
  · exact unary_cont_closed unaryR unaryE sealRoute
  · constructor
    · cases handoffRoute
      exact hsame_refl (append R A)
    · exact pkgSig

end BEDC.Derived.LocatedSupremumUp
