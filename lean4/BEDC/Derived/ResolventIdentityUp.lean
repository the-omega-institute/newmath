import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ResolventIdentityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ResolventIdentityCarrier_two_sided_law [AskSetup] [PackageSetup]
    {X T lam mu A_lam A_mu U_lam U_mu I D _H C P _N I' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (carrier :
      UnaryHistory X ∧ UnaryHistory T ∧ UnaryHistory lam ∧ UnaryHistory mu ∧
        UnaryHistory A_lam ∧ UnaryHistory A_mu ∧ UnaryHistory U_lam ∧
          UnaryHistory U_mu ∧ UnaryHistory I ∧ UnaryHistory D ∧ Cont U_lam U_mu I ∧
            Cont X T C ∧ PkgSig bundle P pkg)
    (sameLedger : Cont U_lam U_mu I') :
    hsame I I' ∧ UnaryHistory I ∧ UnaryHistory I' ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  obtain ⟨_xUnary, _tUnary, _lamUnary, _muUnary, _aLamUnary, _aMuUnary, uLamUnary,
    uMuUnary, iUnary, _dUnary, identityLedger, _carrierReplay, pkgSig⟩ := carrier
  have sameIdentity : hsame I I' :=
    cont_deterministic identityLedger sameLedger
  have iPrimeUnary : UnaryHistory I' :=
    unary_cont_closed uLamUnary uMuUnary sameLedger
  exact ⟨sameIdentity, iUnary, iPrimeUnary, pkgSig⟩

end BEDC.Derived.ResolventIdentityUp
