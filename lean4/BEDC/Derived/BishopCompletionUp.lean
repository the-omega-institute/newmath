import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopCompletionCarrier_filter_compatibility [AskSetup] [PackageSetup]
    {R S D E F U H C P N F' : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (carrier :
      UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory E ∧
        UnaryHistory F ∧ UnaryHistory U ∧ UnaryHistory H ∧ UnaryHistory C ∧
          UnaryHistory P ∧ UnaryHistory N ∧ Cont S R D ∧ Cont D E F ∧ Cont F U C ∧
            PkgSig bundle P pkg)
    (sameFilter : Cont D E F') :
    hsame F F' ∧ UnaryHistory F ∧ UnaryHistory F' ∧ Cont S R D ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  obtain ⟨_rUnary, _sUnary, dUnary, eUnary, fUnary, _uUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, streamRoute, filterRoute, _universalRoute, pkgSig⟩ := carrier
  have sameFiniteFilter : hsame F F' :=
    cont_deterministic filterRoute sameFilter
  have fPrimeUnary : UnaryHistory F' :=
    unary_cont_closed dUnary eUnary sameFilter
  exact ⟨sameFiniteFilter, fUnary, fPrimeUnary, streamRoute, pkgSig⟩

end BEDC.Derived.BishopCompletionUp
