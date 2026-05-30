import BEDC.Derived.ContractionMappingUp.OrbitReadiness

namespace BEDC.Derived.ContractionMappingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ContractionMappingRegularCauchyModulusSurface
    (modulus picard transport replay tailBound exportRead : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont
  UnaryHistory modulus ∧ UnaryHistory picard ∧ UnaryHistory transport ∧
    UnaryHistory replay ∧ UnaryHistory tailBound ∧ UnaryHistory exportRead ∧
      Cont picard modulus tailBound ∧ Cont tailBound transport exportRead

theorem ContractionMappingRegularCauchyModulusSurface_export_route
    [AskSetup] [PackageSetup]
    {X d T G lambda M I H C P N tailBound exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContractionMappingCarrier X d T G lambda M I H C P N bundle pkg →
      Cont I M tailBound →
        Cont tailBound H exportRead →
          PkgSig bundle exportRead pkg →
            ContractionMappingRegularCauchyModulusSurface M I H C tailBound exportRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle exportRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier tailRoute exportRoute exportPkg
  obtain ⟨_XUnary, _dUnary, _TUnary, _GUnary, _lambdaUnary, MUnary, IUnary, HUnary,
    CUnary, _PUnary, _NUnary, provenancePkg⟩ := carrier
  have tailUnary : UnaryHistory tailBound :=
    unary_cont_closed IUnary MUnary tailRoute
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed tailUnary HUnary exportRoute
  exact
    ⟨⟨MUnary, IUnary, HUnary, CUnary, tailUnary, exportUnary, tailRoute, exportRoute⟩,
      provenancePkg, exportPkg⟩

end BEDC.Derived.ContractionMappingUp
