import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LiminfUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LiminfCarrier [AskSetup] [PackageSetup]
    (sequence lowerCut dyadic terminal transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory sequence ∧ UnaryHistory lowerCut ∧ UnaryHistory dyadic ∧
    UnaryHistory terminal ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont sequence lowerCut dyadic ∧
        Cont dyadic terminal replay ∧ PkgSig bundle provenance pkg

theorem LiminfCarrier_route_rows [AskSetup] [PackageSetup]
    {sequence lowerCut dyadic terminal transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LiminfCarrier sequence lowerCut dyadic terminal transport replay provenance localName
        bundle pkg ->
      Cont sequence lowerCut dyadic ∧ Cont dyadic terminal replay ∧
        PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig LiminfCarrier
  intro carrier
  exact ⟨carrier.right.right.right.right.right.right.right.right.left,
    carrier.right.right.right.right.right.right.right.right.right.left,
    carrier.right.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.LiminfUp
