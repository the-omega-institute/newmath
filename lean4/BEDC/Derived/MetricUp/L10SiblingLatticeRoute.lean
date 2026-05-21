import BEDC.Derived.MetricUp
import BEDC.FKernel.Package

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem MetricspaceL10SiblingLatticeRoute_finite_packet [AskSetup] [PackageSetup]
    {located sone real stream regseq dyadic route provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory located ->
      UnaryHistory sone ->
        UnaryHistory stream ->
          UnaryHistory dyadic ->
            UnaryHistory provenance ->
              Cont located sone real ->
                Cont real stream regseq ->
                  Cont regseq dyadic route ->
                    Cont route provenance endpoint ->
                      PkgSig bundle endpoint pkg ->
                        UnaryHistory real ∧ UnaryHistory regseq ∧ UnaryHistory route ∧
                          UnaryHistory endpoint ∧ Cont located sone real ∧
                            Cont real stream regseq ∧ Cont regseq dyadic route ∧
                              Cont route provenance endpoint ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro locatedUnary soneUnary streamUnary dyadicUnary provenanceUnary locatedSoneReal
    realStreamRegseq regseqDyadicRoute routeProvenanceEndpoint endpointPkg
  have realUnary : UnaryHistory real :=
    unary_cont_closed locatedUnary soneUnary locatedSoneReal
  have regseqUnary : UnaryHistory regseq :=
    unary_cont_closed realUnary streamUnary realStreamRegseq
  have routeUnary : UnaryHistory route :=
    unary_cont_closed regseqUnary dyadicUnary regseqDyadicRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceEndpoint
  exact
    ⟨realUnary, regseqUnary, routeUnary, endpointUnary, locatedSoneReal, realStreamRegseq,
      regseqDyadicRoute, routeProvenanceEndpoint, endpointPkg⟩

end BEDC.Derived.MetricUp
