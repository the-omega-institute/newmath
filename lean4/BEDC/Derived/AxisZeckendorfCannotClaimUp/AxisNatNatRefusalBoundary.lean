import BEDC.Derived.AxisZeckendorfCannotClaimUp

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxisZeckendorfCannotClaimRegistryPacket_axisnat_nat_refusal_boundary
    [AskSetup] [PackageSetup]
    {a b c d e f g h p n natRead audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      hsame natRead f ->
        Cont h p audit ->
          PkgSig bundle audit pkg ->
            UnaryHistory f ∧ UnaryHistory natRead ∧ Cont e f h ∧ Cont h p audit ∧
              hsame p n ∧ PkgSig bundle p pkg ∧ PkgSig bundle audit pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro packet sameNatReadF hProvenanceAudit auditPkg
  obtain
    ⟨_aUnary, _bUnary, _cUnary, _dUnary, _eUnary, fUnary, _gUnary, _routeAB, _routeCD,
      routeEF, _pUnary, sameProvenanceName, provenancePkg⟩ := packet
  have natReadUnary : UnaryHistory natRead :=
    unary_transport fUnary (hsame_symm sameNatReadF)
  exact
    ⟨fUnary, natReadUnary, routeEF, hProvenanceAudit, sameProvenanceName, provenancePkg,
      auditPkg⟩

end BEDC.Derived.AxisZeckendorfCannotClaimUp
