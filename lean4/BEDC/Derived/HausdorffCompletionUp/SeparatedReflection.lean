import BEDC.Derived.HausdorffCompletionUp

namespace BEDC.Derived.HausdorffCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HausdorffCompletionCarrier_separated_reflection [AskSetup] [PackageSetup]
    {source entourage separated handoff transport route provenance reflected : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffCompletionCarrier source entourage separated handoff transport route provenance
        bundle pkg ->
      Cont separated provenance reflected ->
        PkgSig bundle reflected pkg ->
          UnaryHistory source ∧ UnaryHistory entourage ∧ UnaryHistory separated ∧
            UnaryHistory handoff ∧ UnaryHistory transport ∧ UnaryHistory route ∧
              UnaryHistory provenance ∧ UnaryHistory reflected ∧
                Cont source entourage transport ∧ Cont separated handoff route ∧
                  Cont transport route provenance ∧ Cont separated provenance reflected ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle reflected pkg ∧
                      SemanticNameCert
                        (fun row : BHist =>
                          hsame row reflected ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                        (fun row : BHist =>
                          Cont separated provenance row ∧
                            HausdorffCompletionCarrier source entourage separated handoff
                              transport route provenance bundle pkg)
                        (fun _row : BHist =>
                          PkgSig bundle reflected pkg ∧
                            Cont separated provenance reflected)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier reflectedRoute reflectedPkg
  have acceptedCarrier :
      HausdorffCompletionCarrier source entourage separated handoff transport route provenance
        bundle pkg := carrier
  obtain ⟨sourceUnary, entourageUnary, separatedUnary, handoffUnary, transportUnary,
    routeUnary, provenanceUnary, sourceEntourageTransport, separatedHandoffRoute,
    transportRouteProvenance, provenancePkg⟩ := carrier
  have reflectedUnary : UnaryHistory reflected :=
    unary_cont_closed separatedUnary provenanceUnary reflectedRoute
  have sourceReflected :
      (fun row : BHist =>
        hsame row reflected ∧ UnaryHistory row ∧ PkgSig bundle row pkg) reflected := by
    exact ⟨hsame_refl reflected, reflectedUnary, reflectedPkg⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row reflected ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        (fun row : BHist =>
          Cont separated provenance row ∧
            HausdorffCompletionCarrier source entourage separated handoff transport route
              provenance bundle pkg)
        (fun _row : BHist => PkgSig bundle reflected pkg ∧
          Cont separated provenance reflected)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro reflected sourceReflected
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same sourceRow
          cases same
          exact sourceRow
      }
      pattern_sound := by
        intro _row sourceRow
        exact
          ⟨cont_result_hsame_transport reflectedRoute (hsame_symm sourceRow.left),
            acceptedCarrier⟩
      ledger_sound := by
        intro _row _sourceRow
        exact ⟨reflectedPkg, reflectedRoute⟩
    }
  exact
    ⟨sourceUnary, entourageUnary, separatedUnary, handoffUnary, transportUnary,
      routeUnary, provenanceUnary, reflectedUnary, sourceEntourageTransport,
      separatedHandoffRoute, transportRouteProvenance, reflectedRoute, provenancePkg,
      reflectedPkg, cert⟩

end BEDC.Derived.HausdorffCompletionUp
