import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessRootExtraction [AskSetup] [PackageSetup]
    {S F sigma mu lambda I Q H C P N sourceRead windowRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier S F sigma mu lambda I Q H C P N bundle pkg ->
      Cont S F sourceRead ->
        Cont sourceRead I windowRead ->
          Cont windowRead Q sealRead ->
            Cont sealRead N namedRead ->
              PkgSig bundle namedRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row F ∨ hsame row sigma ∨ hsame row mu ∨
                        hsame row lambda ∨ hsame row I ∨ hsame row Q ∨
                          hsame row sealRead ∨ hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont S F sourceRead ∧
                        Cont sourceRead I windowRead ∧ Cont windowRead Q sealRead ∧
                          Cont sealRead N namedRead ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle namedRead pkg)
                    hsame ∧
                  UnaryHistory sourceRead ∧ UnaryHistory windowRead ∧
                    UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BoundedMonotoneCauchyWitnessCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sourceRoute windowRoute sealRoute namedRoute namedPkg
  obtain ⟨SUnary, FUnary, _sigmaUnary, _muUnary, _lambdaUnary, IUnary, QUnary,
    _PUnary, sourceScheduleRegular, _regularWitnessTrap, trapSealRoute,
    transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory C :=
    unary_cont_closed IUnary QUnary trapSealRoute
  have NUnary : UnaryHistory N :=
    (unary_cont_factors_from_result transportLocalCertRoute routeUnary).right
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed SUnary FUnary sourceRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary IUnary windowRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary QUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary NUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row F ∨ hsame row sigma ∨ hsame row mu ∨
              hsame row lambda ∨ hsame row I ∨ hsame row Q ∨ hsame row sealRead ∨
                hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S F sourceRead ∧ Cont sourceRead I windowRead ∧
              Cont windowRead Q sealRead ∧ Cont sealRead N namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceRoute, windowRoute, sealRoute, namedRoute, provenancePkg,
          namedPkg⟩
  }
  exact ⟨cert, sourceUnary, windowUnary, sealUnary, namedUnary⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
