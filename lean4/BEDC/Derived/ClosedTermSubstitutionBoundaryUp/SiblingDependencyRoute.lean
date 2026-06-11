import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedTermSubstitutionBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundarySiblingDependencyRoute [AskSetup] [PackageSetup]
    {source value depth shift substitution siblingSurface criticalRead boundaryRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.ClosedtermsubstitutionboundaryUp.ClosedTermSubstitutionBoundaryClassifier
        source value depth shift substitution ->
      Cont shift substitution siblingSurface ->
        Cont siblingSurface depth criticalRead ->
          Cont criticalRead value boundaryRoute ->
            PkgSig bundle criticalRead pkg ->
              PkgSig bundle boundaryRoute pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row boundaryRoute ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row siblingSurface ∨ hsame row criticalRead ∨
                        hsame row boundaryRoute)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont shift substitution siblingSurface ∧
                        Cont siblingSurface depth criticalRead ∧
                          Cont criticalRead value boundaryRoute ∧
                            PkgSig bundle boundaryRoute pkg)
                    hsame ∧
                  UnaryHistory siblingSurface ∧ UnaryHistory criticalRead ∧
                    UnaryHistory boundaryRoute := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro classifier shiftSubstitutionSibling siblingDepthCritical criticalValueBoundary
    _criticalPkg boundaryPkg
  obtain ⟨_sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have siblingUnary : UnaryHistory siblingSurface :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionSibling
  have criticalUnary : UnaryHistory criticalRead :=
    unary_cont_closed siblingUnary depthUnary siblingDepthCritical
  have boundaryUnary : UnaryHistory boundaryRoute :=
    unary_cont_closed criticalUnary valueUnary criticalValueBoundary
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRoute ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row siblingSurface ∨ hsame row criticalRead ∨ hsame row boundaryRoute)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont shift substitution siblingSurface ∧
              Cont siblingSurface depth criticalRead ∧ Cont criticalRead value boundaryRoute ∧
                PkgSig bundle boundaryRoute pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro boundaryRoute ⟨hsame_refl boundaryRoute, boundaryUnary⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, shiftSubstitutionSibling, siblingDepthCritical,
          criticalValueBoundary, boundaryPkg⟩
  }
  exact ⟨cert, siblingUnary, criticalUnary, boundaryUnary⟩

end BEDC.Derived.ClosedTermSubstitutionBoundaryUp
