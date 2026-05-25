import BEDC.Derived.RealOneUp.TasteGate
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RealOneUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealOneRationalEmbeddingRoute [AskSetup] [PackageSetup]
    {q s r d e _h _c p _n : BHist}
    {bundle : ProbeBundle ProbeName}
    {pkg : Pkg}
    (qUnary : UnaryHistory q)
    (sUnary : UnaryHistory s)
    (dUnary : UnaryHistory d)
    (qsr : Cont q s r)
    (rde : Cont r d e)
    (pPkg : PkgSig bundle p pkg)
    (ePkg : PkgSig bundle e pkg) :
    UnaryHistory q ∧ UnaryHistory s ∧ UnaryHistory r ∧ UnaryHistory d ∧
      UnaryHistory e ∧ Cont q s r ∧ Cont r d e ∧ PkgSig bundle p pkg ∧
        PkgSig bundle e pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  have rUnary : UnaryHistory r :=
    unary_cont_closed qUnary sUnary qsr
  have eUnary : UnaryHistory e :=
    unary_cont_closed rUnary dUnary rde
  exact ⟨qUnary, sUnary, rUnary, dUnary, eUnary, qsr, rde, pPkg, ePkg⟩

end BEDC.Derived.RealOneUp
