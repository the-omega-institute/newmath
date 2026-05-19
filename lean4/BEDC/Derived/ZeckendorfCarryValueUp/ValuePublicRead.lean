import BEDC.Derived.ZeckendorfCarryValueUp.NameCertPackage
import BEDC.FKernel.Unary

namespace BEDC.Derived.ZeckendorfCarryValueUp

open BEDC.Derived.AxisZeckendorf.Carry
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZeckendorfCarryValueCarrier_value_public_read [AskSetup] [PackageSetup]
    {source target carry sourceNormal targetNormal valueRow boundary route provenance nameCert
      valueRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZCarry source target ->
      UnaryHistory carry ->
        UnaryHistory valueRow ->
          UnaryHistory route ->
            UnaryHistory provenance ->
              Cont carry valueRow valueRead ->
                Cont valueRead route publicRead ->
                  PkgSig bundle provenance pkg ->
                    PkgSig bundle publicRead pkg ->
                      ∃ packet : ZeckendorfCarryValueUp,
                        packet =
                            ZeckendorfCarryValueUp.mk source target carry sourceNormal
                              targetNormal valueRow boundary route provenance nameCert ∧
                          ¬ hsame source target ∧ UnaryHistory valueRead ∧
                            UnaryHistory publicRead ∧ Cont carry valueRow valueRead ∧
                              Cont valueRead route publicRead ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory ZCarry
  intro sourceTargetCarry carryUnary valueRowUnary routeUnary _provenanceUnary valueRoute
    publicRoute provenancePkg publicPkg
  have notSame : ¬ hsame source target :=
    zCarry_not_hsame sourceTargetCarry
  have valueUnary : UnaryHistory valueRead :=
    unary_cont_closed carryUnary valueRowUnary valueRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed valueUnary routeUnary publicRoute
  exact
    ⟨ZeckendorfCarryValueUp.mk source target carry sourceNormal targetNormal valueRow
        boundary route provenance nameCert,
      rfl, notSame, valueUnary, publicUnary, valueRoute, publicRoute, provenancePkg,
      publicPkg⟩

end BEDC.Derived.ZeckendorfCarryValueUp
