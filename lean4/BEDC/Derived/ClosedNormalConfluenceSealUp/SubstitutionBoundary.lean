import BEDC.Derived.ClosedNormalConfluenceSealUp.NormalSource

namespace BEDC.Derived.ClosedNormalConfluenceSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedNormalConfluenceSealSubstitutionBoundary [AskSetup] [PackageSetup]
    {source normal routeLeft routeRight join transports continuations provenance nameCert
      substitutionRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source ->
      UnaryHistory normal ->
        UnaryHistory routeRight ->
          UnaryHistory transports ->
            UnaryHistory continuations ->
              Cont source normal routeLeft ->
                Cont routeLeft routeRight join ->
                  Cont join transports substitutionRead ->
                    Cont substitutionRead continuations boundaryRead ->
                      PkgSig bundle provenance pkg ->
                        PkgSig bundle boundaryRead pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨
                                  hsame row routeRight ∨ hsame row join ∨
                                    hsame row substitutionRead ∨ hsame row boundaryRead ∨
                                      hsame row provenance)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont join transports substitutionRead ∧
                                  Cont substitutionRead continuations boundaryRead ∧
                                    PkgSig bundle boundaryRead pkg)
                              hsame ∧
                            UnaryHistory routeLeft ∧ UnaryHistory join ∧
                              UnaryHistory substitutionRead ∧ UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro sourceUnary normalUnary routeRightUnary transportsUnary continuationsUnary
    sourceNormalRoute routeJoin joinTransportSubstitution substitutionContinuationBoundary
    _provenancePkg boundaryPkg
  have routeLeftUnary : UnaryHistory routeLeft :=
    unary_cont_closed sourceUnary normalUnary sourceNormalRoute
  have joinUnary : UnaryHistory join :=
    unary_cont_closed routeLeftUnary routeRightUnary routeJoin
  have substitutionUnary : UnaryHistory substitutionRead :=
    unary_cont_closed joinUnary transportsUnary joinTransportSubstitution
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed substitutionUnary continuationsUnary substitutionContinuationBoundary
  have sourceBoundary :
      (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row) boundaryRead := by
    exact ⟨hsame_refl boundaryRead, boundaryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨
              hsame row routeRight ∨ hsame row join ∨ hsame row substitutionRead ∨
                hsame row boundaryRead ∨ hsame row provenance)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont join transports substitutionRead ∧
              Cont substitutionRead continuations boundaryRead ∧
                PkgSig bundle boundaryRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead sourceBoundary
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inl source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, joinTransportSubstitution, substitutionContinuationBoundary,
          boundaryPkg⟩
  }
  exact ⟨cert, routeLeftUnary, joinUnary, substitutionUnary, boundaryUnary⟩

end BEDC.Derived.ClosedNormalConfluenceSealUp
