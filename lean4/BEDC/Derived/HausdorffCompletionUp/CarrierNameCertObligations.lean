import BEDC.Derived.HausdorffCompletionUp

namespace BEDC.Derived.HausdorffCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HausdorffCompletionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source entourage separated handoff transport route provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffCompletionCarrier source entourage separated handoff transport route provenance
        bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row provenance ∧
              HausdorffCompletionCarrier source entourage separated handoff transport route
                provenance bundle pkg)
          (fun row : BHist =>
            hsame row provenance ∧ Cont source entourage transport ∧
              Cont separated handoff route)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory source ∧ UnaryHistory entourage ∧ UnaryHistory separated ∧
          UnaryHistory handoff ∧ UnaryHistory transport ∧ UnaryHistory route ∧
            UnaryHistory provenance ∧ Cont source entourage transport ∧
              Cont separated handoff route ∧ Cont transport route provenance ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro carrier
  have carrierFull :
      HausdorffCompletionCarrier source entourage separated handoff transport route provenance
        bundle pkg :=
    carrier
  obtain ⟨sourceUnary, entourageUnary, separatedUnary, handoffUnary, transportUnary,
    routeUnary, provenanceUnary, sourceEntourageTransport, separatedHandoffRoute,
    transportRouteProvenance, provenancePkg⟩ := carrier
  have sourceAtProvenance :
      (fun row : BHist =>
        hsame row provenance ∧
          HausdorffCompletionCarrier source entourage separated handoff transport route
            provenance bundle pkg) provenance :=
    And.intro (hsame_refl provenance) carrierFull
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row provenance ∧
              HausdorffCompletionCarrier source entourage separated handoff transport route
                provenance bundle pkg)
          (fun row : BHist =>
            hsame row provenance ∧ Cont source entourage transport ∧
              Cont separated handoff route)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance sourceAtProvenance
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _row' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
    }
    pattern_sound := by
      intro _row source
      exact And.intro source.left
        (And.intro sourceEntourageTransport separatedHandoffRoute)
    ledger_sound := by
      intro _row source
      exact And.intro source.left provenancePkg
  }
  exact And.intro cert
    (And.intro sourceUnary
      (And.intro entourageUnary
        (And.intro separatedUnary
          (And.intro handoffUnary
            (And.intro transportUnary
              (And.intro routeUnary
                (And.intro provenanceUnary
                  (And.intro sourceEntourageTransport
                    (And.intro separatedHandoffRoute
                      (And.intro transportRouteProvenance provenancePkg))))))))))

end BEDC.Derived.HausdorffCompletionUp
