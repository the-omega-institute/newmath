import BEDC.Derived.SpinGroupUp

namespace BEDC.Derived.SpinGroupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SpinGroupRootCarrier_conjugation_action_identity_law [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger identityAction :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      hsame groupWord BHist.Empty ->
        Cont BHist.Empty vector identityAction ->
          UnaryHistory identityAction ∧ hsame identityAction vector ∧ PkgSig bundle ledger pkg := by
  intro carrier sameGroup identityCont
  have cliffordExact :=
    BEDC.Derived.CliffordUp.CliffordCarrierPackage_universal_ledger_exactness carrier.left
  have identitySame : hsame identityAction vector :=
    cont_left_unit_result identityCont
  have identityUnary : UnaryHistory identityAction :=
    unary_transport cliffordExact.right.left (hsame_symm identitySame)
  exact And.intro identityUnary
    (And.intro identitySame carrier.right.right.right)

end BEDC.Derived.SpinGroupUp
