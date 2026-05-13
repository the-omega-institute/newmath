import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UnaryZeroSpineStandardIsoUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UnaryZeroSpineStandardIsoCarrier [AskSetup] [PackageSetup]
    (unary axis length forward backward transport routes provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory unary ∧ UnaryHistory axis ∧ UnaryHistory length ∧ UnaryHistory provenance ∧
    UnaryHistory cert ∧ Cont unary length forward ∧ Cont axis length backward ∧
      Cont forward backward routes ∧ Cont routes cert provenance ∧
        Cont provenance cert transport ∧ PkgSig bundle routes pkg

theorem UnaryZeroSpineStandardIsoCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {unary axis length forward backward transport routes provenance cert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryZeroSpineStandardIsoCarrier unary axis length forward backward transport routes provenance
        cert bundle pkg ->
      Cont routes cert endpoint ->
        PkgSig bundle endpoint pkg ->
          SemanticNameCert
              (fun row : BHist =>
                UnaryZeroSpineStandardIsoCarrier unary axis length forward backward transport
                  routes provenance cert bundle pkg ∧ hsame row endpoint)
              (fun row : BHist => hsame row provenance)
              (fun row : BHist => hsame row provenance ∧ PkgSig bundle endpoint pkg)
              hsame ∧
            UnaryHistory unary ∧ UnaryHistory axis ∧ UnaryHistory length ∧
              UnaryHistory endpoint ∧ Cont unary length forward ∧
                Cont axis length backward ∧ Cont routes cert endpoint := by
  intro carrier routesCert endpointPkg
  cases carrier with
  | intro unaryRow rest =>
  cases rest with
  | intro axisRow rest =>
  cases rest with
  | intro lengthRow rest =>
  cases rest with
  | intro provenanceUnary rest =>
  cases rest with
  | intro certUnary rest =>
  cases rest with
  | intro forwardRow rest =>
  cases rest with
  | intro backwardRow rest =>
  cases rest with
  | intro routesRow rest =>
  cases rest with
  | intro provenanceRow rest =>
  cases rest with
  | intro transportRow routesPkg =>
  have forwardUnary : UnaryHistory forward :=
    unary_cont_closed unaryRow lengthRow forwardRow
  have backwardUnary : UnaryHistory backward :=
    unary_cont_closed axisRow lengthRow backwardRow
  have routesUnary : UnaryHistory routes :=
    unary_cont_closed forwardUnary backwardUnary routesRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed routesUnary certUnary routesCert
  have sourceAtEndpoint :
      (fun row : BHist =>
        UnaryZeroSpineStandardIsoCarrier unary axis length forward backward transport routes
          provenance cert bundle pkg ∧ hsame row endpoint) endpoint :=
    And.intro
      (And.intro unaryRow
        (And.intro axisRow
          (And.intro lengthRow
            (And.intro provenanceUnary
              (And.intro certUnary
                (And.intro forwardRow
                  (And.intro backwardRow
                    (And.intro routesRow
                      (And.intro provenanceRow
                        (And.intro transportRow routesPkg))))))))))
      (hsame_refl endpoint)
  have provenanceSame : hsame endpoint provenance :=
    hsame_symm (cont_deterministic provenanceRow routesCert)
  have certSurface :
      SemanticNameCert
        (fun row : BHist =>
          UnaryZeroSpineStandardIsoCarrier unary axis length forward backward transport routes
            provenance cert bundle pkg ∧ hsame row endpoint)
        (fun row : BHist => hsame row provenance)
        (fun row : BHist => hsame row provenance ∧ PkgSig bundle endpoint pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint sourceAtEndpoint
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro row sourceRow
      exact hsame_trans sourceRow.right provenanceSame
    ledger_sound := by
      intro row sourceRow
      exact And.intro (hsame_trans sourceRow.right provenanceSame) endpointPkg
  }
  exact And.intro certSurface
    (And.intro unaryRow
      (And.intro axisRow
        (And.intro lengthRow
          (And.intro endpointUnary
            (And.intro forwardRow
              (And.intro backwardRow routesCert))))))

end BEDC.Derived.UnaryZeroSpineStandardIsoUp
