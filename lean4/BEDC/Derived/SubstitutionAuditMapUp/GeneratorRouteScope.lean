import BEDC.Derived.SubstitutionAuditMapUp.Core

namespace BEDC.Derived.SubstitutionAuditMapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubstitutionAuditMapCarrier_generator_route_scope [AskSetup] [PackageSetup]
    {term closed shift substitute composition generator transport route provenance name
      generatorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubstitutionAuditMapCarrier term closed shift substitute composition generator transport route
        provenance name bundle pkg ->
      Cont generator route generatorRead ->
        PkgSig bundle generatorRead pkg ->
          UnaryHistory generator ∧ UnaryHistory route ∧ UnaryHistory generatorRead ∧
            hsame composition generator ∧ Cont generator route generatorRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle generatorRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier generatorRoute generatorPkg
  obtain ⟨_termUnary, _closedUnary, _shiftUnary, _substituteUnary, compositionUnary,
    generatorUnary, _transportUnary, routeUnary, _provenanceUnary, _nameUnary,
    _termClosed, _shiftSubstitute, compositionGenerator, _transportRoute, _provenanceName,
    _nameGenerator, provenancePkg, _namePkg⟩ := carrier
  have generatorReadUnary : UnaryHistory generatorRead :=
    unary_cont_closed generatorUnary routeUnary generatorRoute
  exact
    ⟨generatorUnary, routeUnary, generatorReadUnary, compositionGenerator, generatorRoute,
      provenancePkg, generatorPkg⟩

end BEDC.Derived.SubstitutionAuditMapUp
