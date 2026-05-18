import BEDC.Derived.AxisZeckendorfCannotClaimUp

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxisZeckendorfCannotClaimRegistryPacket_dimlift_primitive_refusal_boundary
    [AskSetup] [PackageSetup] {a b c d e f g h p n dimRead audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      hsame dimRead g ->
        Cont h p audit ->
          PkgSig bundle audit pkg ->
            UnaryHistory g ∧ UnaryHistory dimRead ∧ UnaryHistory h ∧ Cont e f h ∧
              Cont h p audit ∧ hsame p n ∧ PkgSig bundle p pkg ∧
                PkgSig bundle audit pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro packet sameDimReadG hProvenanceAudit auditPkg
  obtain
    ⟨aUnary, bUnary, _cUnary, _dUnary, _eUnary, _fUnary, gUnary, routeAB, _routeCD,
      routeEF, pUnary, sameProvenanceName, provenancePkg⟩ := packet
  have dimReadUnary : UnaryHistory dimRead :=
    unary_transport gUnary (hsame_symm sameDimReadG)
  have hUnary : UnaryHistory h :=
    unary_cont_closed aUnary bUnary routeAB
  exact
    ⟨gUnary, dimReadUnary, hUnary, routeEF, hProvenanceAudit, sameProvenanceName,
      provenancePkg, auditPkg⟩

end BEDC.Derived.AxisZeckendorfCannotClaimUp
