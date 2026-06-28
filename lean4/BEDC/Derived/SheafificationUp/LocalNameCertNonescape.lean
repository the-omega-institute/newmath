import BEDC.Derived.SheafificationUp.TasteGate

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.FKernel.Bundle
open BEDC.FKernel.Ask

theorem SheafificationLocalNameCertNonescape [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N row : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (carrier : SheafificationCarrier C T J P L G S H R Q N bundle pkg)
    (named : hsame row N) :
    UnaryHistory row ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist hsame Pkg
  have unaryN : UnaryHistory N :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have pkgN : PkgSig bundle N pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right
  exact ⟨unary_transport_symm unaryN named, pkgN⟩

end BEDC.Derived.SheafificationUp
