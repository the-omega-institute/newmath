import BEDC.Derived.CompactNetModulusSelectorUp.KernelCarrier

namespace BEDC.Derived.CompactNetModulusSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactNetModulusSelectorCenterLedgerExposure [AskSetup] [PackageSetup]
    {X Y E C R M F foldRow D H Q P N centerRead radiusRead precisionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactNetModulusSelectorCarrier X Y E C R M F foldRow D H Q P N bundle pkg ->
      Cont C R centerRead ->
        Cont centerRead M radiusRead ->
          Cont radiusRead D precisionRead ->
            PkgSig bundle precisionRead pkg ->
              UnaryHistory C ∧ UnaryHistory R ∧ UnaryHistory M ∧ UnaryHistory D ∧
                UnaryHistory centerRead ∧ UnaryHistory radiusRead ∧
                  UnaryHistory precisionRead ∧ Cont C R centerRead ∧
                    Cont centerRead M radiusRead ∧ Cont radiusRead D precisionRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle precisionRead pkg := by
  -- BEDC touchpoint anchor: CompactNetModulusSelectorCarrier BHist ProbeBundle Pkg Cont PkgSig
  intro carrier centerRoute radiusRoute precisionRoute precisionPkg
  obtain ⟨_XUnary, _YUnary, _EUnary, CUnary, RUnary, MUnary, _FUnary, _foldUnary, DUnary,
    _HUnary, _QUnary, _PUnary, _NUnary, _sourceProbesCenters, _moduliFoldPrecision,
    _precisionRouteName, provenancePkg⟩ := carrier
  have centerUnary : UnaryHistory centerRead :=
    unary_cont_closed CUnary RUnary centerRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed centerUnary MUnary radiusRoute
  have precisionUnary : UnaryHistory precisionRead :=
    unary_cont_closed radiusUnary DUnary precisionRoute
  exact
    ⟨CUnary, RUnary, MUnary, DUnary, centerUnary, radiusUnary, precisionUnary, centerRoute,
      radiusRoute, precisionRoute, provenancePkg, precisionPkg⟩

end BEDC.Derived.CompactNetModulusSelectorUp
