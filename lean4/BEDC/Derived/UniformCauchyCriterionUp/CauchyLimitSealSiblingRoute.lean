import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_cauchy_limit_seal_sibling_route [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name siblingWindow
      cauchyLimitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont windows tail siblingWindow →
        Cont siblingWindow sealRow cauchyLimitRead →
          PkgSig bundle siblingWindow pkg →
            PkgSig bundle cauchyLimitRead pkg →
              UnaryHistory windows ∧ UnaryHistory tail ∧ UnaryHistory siblingWindow ∧
                UnaryHistory cauchyLimitRead ∧ Cont index windows modulus ∧
                  Cont modulus tolerance tail ∧ Cont windows tail siblingWindow ∧
                    Cont siblingWindow sealRow cauchyLimitRead ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle siblingWindow pkg ∧ PkgSig bundle cauchyLimitRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet windowsTailSibling siblingSealRead siblingPkg sealPkg
  obtain ⟨_indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have siblingUnary : UnaryHistory siblingWindow :=
    unary_cont_closed windowsUnary tailUnary windowsTailSibling
  have sealReadUnary : UnaryHistory cauchyLimitRead :=
    unary_cont_closed siblingUnary sealRowUnary siblingSealRead
  exact
    ⟨windowsUnary, tailUnary, siblingUnary, sealReadUnary, indexWindowsModulus,
      modulusToleranceTail, windowsTailSibling, siblingSealRead, namePkg, siblingPkg, sealPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
