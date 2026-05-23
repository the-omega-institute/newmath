import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberDyadicCoverUniformModulusHandoff [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow dyadicRead compactRead
      uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont cover radius dyadicRead →
        Cont dyadicRead mesh compactRead →
          Cont compactRead nameRow uniformRead →
            PkgSig bundle uniformRead pkg →
              UnaryHistory cover ∧ UnaryHistory radius ∧ UnaryHistory dyadicRead ∧
                UnaryHistory compactRead ∧ UnaryHistory uniformRead ∧
                  Cont cover window radius ∧ Cont cover radius dyadicRead ∧
                    Cont dyadicRead mesh compactRead ∧ Cont compactRead nameRow uniformRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier coverRadiusDyadic dyadicMeshCompact compactNameUniform uniformPkg
  obtain ⟨coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, nameRowUnary, coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed coverUnary radiusUnary coverRadiusDyadic
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed dyadicUnary meshUnary dyadicMeshCompact
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactUnary nameRowUnary compactNameUniform
  exact
    ⟨coverUnary, radiusUnary, dyadicUnary, compactUnary, uniformUnary,
      coverWindowRadius, coverRadiusDyadic, dyadicMeshCompact, compactNameUniform,
      provenancePkg, uniformPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
