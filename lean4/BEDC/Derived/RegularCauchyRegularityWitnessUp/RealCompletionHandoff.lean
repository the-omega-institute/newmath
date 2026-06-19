import BEDC.Derived.RegularCauchyRegularityWitnessUp.NameCertObligations

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyRegularityWitnessUp

theorem RegularCauchyRegularityWitnessRealCompletionHandoff [AskSetup] [PackageSetup]
    {S mu j Omega R Q E H C P N completionRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyRegularityWitnessCarrier S mu j Omega R Q E H C P N bundle pkg ->
      Cont R Q completionRead ->
        Cont completionRead E sealRead ->
          PkgSig bundle sealRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row S ∨ hsame row Omega ∨ hsame row R ∨ hsame row Q ∨
                    hsame row E ∨ hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont R Q completionRead ∧
                    Cont completionRead E sealRead ∧ PkgSig bundle sealRead pkg)
                hsame ∧
              UnaryHistory completionRead ∧ UnaryHistory sealRead ∧
                Cont R Q completionRead ∧ Cont completionRead E sealRead ∧
                  PkgSig bundle N pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier completionRoute sealRoute sealPkg
  obtain ⟨_sUnary, _muUnary, _jUnary, _omegaUnary, rUnary, qUnary, eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _sourceRoute, _windowRoute, _toleranceRoute,
    _transportRoute, _provenancePkg, namePkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed rUnary qUnary completionRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed completionUnary eUnary sealRoute
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row Omega ∨ hsame row R ∨ hsame row Q ∨
              hsame row E ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R Q completionRead ∧
              Cont completionRead E sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSeal
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
        intro _row _other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, completionRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, completionUnary, sealUnary, completionRoute, sealRoute, namePkg, sealPkg⟩

theorem RegularCauchyRegularityWitness_real_completion_handoff [AskSetup] [PackageSetup]
    {S mu j Omega R Q E H C P N completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyRegularityWitnessCarrier S mu j Omega R Q E H C P N bundle pkg →
      Cont E N completionRead →
        PkgSig bundle completionRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row S ∨ hsame row Omega ∨ hsame row R ∨ hsame row Q ∨
                  hsame row E ∨ hsame row completionRead)
              (fun row : BHist => hsame row completionRead ∧ PkgSig bundle completionRead pkg)
              hsame ∧
            UnaryHistory completionRead ∧ Cont S mu j ∧ Cont j Omega R ∧ Cont R Q E ∧
              Cont E H C ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier completionRoute completionPkg
  obtain ⟨_unaryS, _unaryMu, _unaryJ, _unaryOmega, _unaryR, _unaryQ, eUnary, _hUnary,
    _cUnary, _pUnary, nUnary, routeSMuJ, routeJOmegaR, routeRQE, routeEHC,
    _pkgP, _pkgN⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed eUnary nUnary completionRoute
  have sourceAtCompletion :
      hsame completionRead completionRead ∧ UnaryHistory completionRead :=
    ⟨hsame_refl completionRead, completionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row Omega ∨ hsame row R ∨ hsame row Q ∨
              hsame row E ∨ hsame row completionRead)
          (fun row : BHist => hsame row completionRead ∧ PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead sourceAtCompletion
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, completionPkg⟩
  }
  exact
    ⟨cert, completionUnary, routeSMuJ, routeJOmegaR, routeRQE, routeEHC, completionPkg⟩

end BEDC.Derived.RegularCauchyRegularityWitnessUp
