import BEDC.Derived.SubjectReductionRouteChoiceUp.ObligationSurface

namespace BEDC.Derived.SubjectReductionRouteChoiceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubjectReductionRouteChoiceVisionHandoff [AskSetup] [PackageSetup]
    {typedTerm sourceType targetType routeLeft routeRight subjectTrace reductionTrace
      substitutionTrace obstruction boundary continuation provenance nameRow visionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubjectReductionRouteChoiceCarrier typedTerm sourceType targetType routeLeft routeRight
        subjectTrace reductionTrace substitutionTrace obstruction boundary continuation provenance
        nameRow bundle pkg →
      Cont substitutionTrace continuation visionRead →
        PkgSig bundle visionRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row visionRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row typedTerm ∨ hsame row sourceType ∨ hsame row targetType ∨
                  hsame row routeLeft ∨ hsame row routeRight ∨ hsame row subjectTrace ∨
                    hsame row reductionTrace ∨ hsame row substitutionTrace ∨
                      hsame row obstruction ∨ hsame row boundary ∨
                        hsame row continuation ∨ hsame row provenance ∨
                          hsame row nameRow ∨ hsame row visionRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont typedTerm sourceType routeLeft ∧
                  Cont routeLeft targetType routeRight ∧
                    Cont subjectTrace reductionTrace substitutionTrace ∧
                      Cont obstruction boundary continuation ∧
                        Cont substitutionTrace continuation visionRead ∧
                          PkgSig bundle visionRead pkg)
              hsame ∧
            UnaryHistory visionRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier visionRoute visionPkg
  obtain ⟨_typedUnary, _sourceUnary, _targetUnary, _routeLeftUnary, _routeRightUnary,
    _subjectUnary, _reductionUnary, substitutionUnary, _obstructionUnary, _boundaryUnary,
    continuationUnary, _provenanceUnary, _nameUnary, typedRoute, targetRoute,
    substitutionRoute, obstructionRoute, _namePkg⟩ := carrier
  have visionUnary : UnaryHistory visionRead :=
    unary_cont_closed substitutionUnary continuationUnary visionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row visionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typedTerm ∨ hsame row sourceType ∨ hsame row targetType ∨
              hsame row routeLeft ∨ hsame row routeRight ∨ hsame row subjectTrace ∨
                hsame row reductionTrace ∨ hsame row substitutionTrace ∨
                  hsame row obstruction ∨ hsame row boundary ∨
                    hsame row continuation ∨ hsame row provenance ∨
                      hsame row nameRow ∨ hsame row visionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont typedTerm sourceType routeLeft ∧
              Cont routeLeft targetType routeRight ∧
                Cont subjectTrace reductionTrace substitutionTrace ∧
                  Cont obstruction boundary continuation ∧
                    Cont substitutionTrace continuation visionRead ∧
                      PkgSig bundle visionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro visionRead ⟨hsame_refl visionRead, visionUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, typedRoute, targetRoute, substitutionRoute, obstructionRoute,
          visionRoute, visionPkg⟩
  }
  exact ⟨cert, visionUnary⟩

end BEDC.Derived.SubjectReductionRouteChoiceUp
