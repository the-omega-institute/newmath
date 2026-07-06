import BEDC.Derived.MollifierUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Package

namespace BEDC.Derived.MollifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MollifierCarrier_kernel_support_envelope [AskSetup] [PackageSetup]
    {S R N P C H L replayRead envelopeRead provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory R →
        UnaryHistory P →
          UnaryHistory H →
            UnaryHistory L →
              Cont S R N →
                Cont N P C →
                  Cont C H replayRead →
                    Cont replayRead L envelopeRead →
                      PkgSig bundle provenance pkg →
                        SemanticNameCert
                            (fun row : BHist =>
                              (hsame row envelopeRead ∨ hsame row provenance) ∧
                                UnaryHistory row)
                            (fun row : BHist =>
                              hsame row S ∨ hsame row R ∨ hsame row N ∨
                                hsame row P ∨ hsame row C ∨ hsame row H ∨
                                  hsame row L ∨ hsame row replayRead ∨
                                    hsame row envelopeRead ∨ hsame row provenance)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont S R N ∧ Cont N P C ∧
                                Cont C H replayRead ∧ Cont replayRead L envelopeRead ∧
                                  PkgSig bundle provenance pkg)
                            hsame ∧
                          UnaryHistory envelopeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro sUnary rUnary pUnary hUnary lUnary supportRoute convolutionRoute replayRoute
    envelopeRoute provenanceSig
  have supportUnary : UnaryHistory N :=
    unary_cont_closed sUnary rUnary supportRoute
  have convolutionUnary : UnaryHistory C :=
    unary_cont_closed supportUnary pUnary convolutionRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed convolutionUnary hUnary replayRoute
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed replayUnary lUnary envelopeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row envelopeRead ∨ hsame row provenance) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row N ∨ hsame row P ∨ hsame row C ∨
              hsame row H ∨ hsame row L ∨ hsame row replayRead ∨
                hsame row envelopeRead ∨ hsame row provenance)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S R N ∧ Cont N P C ∧ Cont C H replayRead ∧
              Cont replayRead L envelopeRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro envelopeRead ⟨Or.inl (hsame_refl envelopeRead), envelopeUnary⟩
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
        constructor
        · cases source.left with
          | inl sameEnvelope =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameEnvelope)
          | inr sameProvenance =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameProvenance)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameEnvelope =>
          exact
            Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
              Or.inr <| Or.inr <| Or.inl sameEnvelope
      | inr sameProvenance =>
          exact
            Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
              Or.inr <| Or.inr <| Or.inr sameProvenance
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, supportRoute, convolutionRoute, replayRoute, envelopeRoute,
          provenanceSig⟩
  }
  exact ⟨cert, envelopeUnary⟩

theorem MollifierCarrier_scoped_kernel_dependency_boundary [AskSetup] [PackageSetup]
    {S R N P C H L replayRead outputRead boundaryRead dependencyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory R →
        UnaryHistory P →
          UnaryHistory H →
            UnaryHistory L →
              Cont S R N →
                Cont N P C →
                  Cont C H replayRead →
                    Cont replayRead L outputRead →
                      Cont outputRead H boundaryRead →
                        PkgSig bundle dependencyRead pkg →
                          SemanticNameCert
                              (fun row : BHist =>
                                (hsame row boundaryRead ∨ hsame row dependencyRead) ∧
                                  UnaryHistory row)
                              (fun row : BHist =>
                                hsame row S ∨ hsame row R ∨ hsame row N ∨
                                  hsame row P ∨ hsame row C ∨ hsame row H ∨
                                    hsame row L ∨ hsame row replayRead ∨
                                      hsame row outputRead ∨ hsame row boundaryRead ∨
                                        hsame row dependencyRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont S R N ∧ Cont N P C ∧
                                  Cont C H replayRead ∧ Cont replayRead L outputRead ∧
                                    Cont outputRead H boundaryRead ∧
                                      PkgSig bundle dependencyRead pkg)
                              hsame ∧
                            UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro sUnary rUnary pUnary hUnary lUnary supportRoute convolutionRoute replayRoute
    outputRoute boundaryRoute dependencySig
  have supportUnary : UnaryHistory N :=
    unary_cont_closed sUnary rUnary supportRoute
  have convolutionUnary : UnaryHistory C :=
    unary_cont_closed supportUnary pUnary convolutionRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed convolutionUnary hUnary replayRoute
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed replayUnary lUnary outputRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed outputUnary hUnary boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row boundaryRead ∨ hsame row dependencyRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row N ∨ hsame row P ∨ hsame row C ∨
              hsame row H ∨ hsame row L ∨ hsame row replayRead ∨
                hsame row outputRead ∨ hsame row boundaryRead ∨ hsame row dependencyRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S R N ∧ Cont N P C ∧ Cont C H replayRead ∧
              Cont replayRead L outputRead ∧ Cont outputRead H boundaryRead ∧
                PkgSig bundle dependencyRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro boundaryRead ⟨Or.inl (hsame_refl boundaryRead), boundaryUnary⟩
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
        constructor
        · cases source.left with
          | inl sameBoundary =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameBoundary)
          | inr sameDependency =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameDependency)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameBoundary =>
          exact
            Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
              Or.inr <| Or.inr <| Or.inr <| Or.inl sameBoundary
      | inr sameDependency =>
          exact
            Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
              Or.inr <| Or.inr <| Or.inr <| Or.inr sameDependency
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, supportRoute, convolutionRoute, replayRoute, outputRoute,
          boundaryRoute, dependencySig⟩
  }
  exact ⟨cert, boundaryUnary⟩

end BEDC.Derived.MollifierUp
