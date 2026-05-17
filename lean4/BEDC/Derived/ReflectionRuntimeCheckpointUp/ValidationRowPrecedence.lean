import BEDC.Derived.ReflectionRuntimeCheckpointUp.Certificate

namespace BEDC.Derived.ReflectionRuntimeCheckpointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ReflectionRuntimeCheckpointCarrier_validation_row_precedence [AskSetup] [PackageSetup]
    {input state trace validation transport route provenance localName checkpointRead
      validationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ReflectionRuntimeCheckpointCarrier input state trace validation transport route provenance
        localName →
      hsame checkpointRead localName →
        PkgSig bundle checkpointRead pkg →
          Cont checkpointRead validation validationRead →
            SemanticNameCert
              (fun row : BHist =>
                ReflectionRuntimeCheckpointCarrier input state trace validation transport route
                    provenance localName ∧
                  hsame row validationRead)
              (fun row : BHist => Cont checkpointRead validation row ∧ hsame checkpointRead localName)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont input state trace ∧ Cont trace validation route ∧
                  PkgSig bundle checkpointRead pkg)
              hsame ∧
              UnaryHistory validationRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier checkpointSame checkpointPkg validationRoute
  have obligations :=
    ReflectionRuntimeCheckpointCarrier_namecert_obligations
      (input := input) (state := state) (trace := trace) (validation := validation)
      (transport := transport) (route := route) (provenance := provenance)
      (localName := localName) (checkpointRead := checkpointRead) (bundle := bundle)
      (pkg := pkg) carrier checkpointSame checkpointPkg
  obtain ⟨inputUnary, stateUnary, traceUnary, validationUnary, checkpointUnary,
    inputStateTrace, traceValidationRoute, _provenanceValidationLocalName,
    _checkpointMatchesValidation, checkpointPkg'⟩ := obligations
  have validationReadUnary : UnaryHistory validationRead :=
    unary_cont_closed checkpointUnary validationUnary validationRoute
  have carrierWitness := carrier
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          ReflectionRuntimeCheckpointCarrier input state trace validation transport route
              provenance localName ∧
            hsame row validationRead)
        (fun row : BHist => Cont checkpointRead validation row ∧ hsame checkpointRead localName)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont input state trace ∧ Cont trace validation route ∧
            PkgSig bundle checkpointRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro validationRead (And.intro carrierWitness (hsame_refl validationRead))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact
        ⟨cont_result_hsame_transport validationRoute (hsame_symm source.right),
          checkpointSame⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport validationReadUnary (hsame_symm source.right), inputStateTrace,
          traceValidationRoute, checkpointPkg'⟩
  }
  exact ⟨cert, validationReadUnary⟩

end BEDC.Derived.ReflectionRuntimeCheckpointUp
