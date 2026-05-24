import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberL10SiblingRoute [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow tailRead streamRead
      regularRead realRead compactRead continuousRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont window radius tailRead →
        Cont tailRead mesh streamRead →
          Cont streamRead route regularRead →
            Cont regularRead transport realRead →
              Cont realRead mesh compactRead →
                Cont compactRead route continuousRead →
                  Cont continuousRead nameRow uniformRead →
                    PkgSig bundle uniformRead pkg →
                      UnaryHistory tailRead ∧ UnaryHistory streamRead ∧
                        UnaryHistory regularRead ∧ UnaryHistory realRead ∧
                          UnaryHistory compactRead ∧ UnaryHistory continuousRead ∧
                            UnaryHistory uniformRead ∧ PkgSig bundle provenance pkg ∧
                              PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier windowRadiusTail tailMeshStream streamRouteRegular regularTransportReal
    realMeshCompact compactRouteContinuous continuousNameUniform uniformPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed windowUnary radiusUnary windowRadiusTail
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed tailUnary meshUnary tailMeshStream
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed streamUnary routeUnary streamRouteRegular
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary transportUnary regularTransportReal
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed realUnary meshUnary realMeshCompact
  have continuousUnary : UnaryHistory continuousRead :=
    unary_cont_closed compactUnary routeUnary compactRouteContinuous
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed continuousUnary nameRowUnary continuousNameUniform
  exact
    ⟨tailUnary, streamUnary, regularUnary, realUnary, compactUnary, continuousUnary,
      uniformUnary, provenancePkg, uniformPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
