import BEDC.Derived.AxisZeckendorfCannotClaimUp

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxisZeckendorfCannotClaimRegistryPacket_fullaxis_real_refusal_boundary
    [AskSetup] [PackageSetup] {a b c d e f g h p n realRead audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg →
      hsame realRead e →
        Cont h p audit →
          PkgSig bundle audit pkg →
            UnaryHistory e ∧ UnaryHistory realRead ∧ Cont e f h ∧ Cont h p audit ∧
              hsame p n ∧ PkgSig bundle p pkg ∧ PkgSig bundle audit pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont PkgSig ProbeBundle UnaryHistory
  intro packet realReadSame auditRoute auditPkg
  obtain
    ⟨_aUnary, _bUnary, _cUnary, _dUnary, eUnary, _fUnary, _gUnary, _routeAB,
      _routeCD, routeEF, _pUnary, sameProvenanceName, provenancePkg⟩ := packet
  have realReadUnary : UnaryHistory realRead :=
    unary_transport_symm eUnary realReadSame
  exact
    ⟨eUnary, realReadUnary, routeEF, auditRoute, sameProvenanceName, provenancePkg,
      auditPkg⟩

end BEDC.Derived.AxisZeckendorfCannotClaimUp
