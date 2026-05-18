import BEDC.Derived.AxisZeckendorfCannotClaimUp

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxisZeckendorfCannotClaimRegistryPacket_horizon_refusal_scope [AskSetup]
    [PackageSetup] {a b c d e f g h p n horizon audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg →
      (hsame horizon e ∨ hsame horizon f ∨ hsame horizon g) →
        Cont h p audit →
          PkgSig bundle audit pkg →
            UnaryHistory horizon ∧ Cont e f h ∧ Cont h p audit ∧ hsame p n ∧
              PkgSig bundle p pkg ∧ PkgSig bundle audit pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle PkgSig
  intro packet horizonSource auditRoute auditPkg
  obtain ⟨_aUnary, _bUnary, _cUnary, _dUnary, eUnary, fUnary, gUnary, _routeAB,
    _routeCD, routeEF, _pUnary, sameProvenanceName, provenancePkg⟩ := packet
  have horizonUnary : UnaryHistory horizon := by
    cases horizonSource with
    | inl sameE =>
        exact unary_transport_symm eUnary sameE
    | inr rest =>
        cases rest with
        | inl sameF =>
            exact unary_transport_symm fUnary sameF
        | inr sameG =>
            exact unary_transport_symm gUnary sameG
  exact
    ⟨horizonUnary, routeEF, auditRoute, sameProvenanceName, provenancePkg, auditPkg⟩

end BEDC.Derived.AxisZeckendorfCannotClaimUp
