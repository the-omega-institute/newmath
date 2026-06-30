import BEDC.Derived.AxiomDependencyTupleUp

namespace BEDC.Derived.AxiomDependencyTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxiomDependencyTuplePkgNameCertScope [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName pkgRead nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg ->
      UnaryHistory provenance -> Cont provenance localName pkgRead ->
        Cont pkgRead route nameRead -> PkgSig bundle pkgRead pkg -> PkgSig bundle nameRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row provenance ∨ hsame row localName ∨ hsame row pkgRead ∨
                  hsame row nameRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont provenance localName pkgRead ∧
                  Cont pkgRead route nameRead ∧ PkgSig bundle pkgRead pkg ∧
                    PkgSig bundle nameRead pkg)
              hsame ∧
            UnaryHistory pkgRead ∧ UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier provenanceUnary provenanceLocalPkg pkgRouteName pkgReadPkg nameReadPkg
  obtain ⟨_modeCases, _modeUnary, _witnessUnary, _supplyUnary, _transportUnary,
    routeUnary, localNameUnary, _transportSame, _modeWitnessRoute, _routeSupplyLocalName,
    provenancePkg⟩ := carrier
  have _provenancePkg : PkgSig bundle provenance pkg := provenancePkg
  have pkgReadUnary : UnaryHistory pkgRead :=
    unary_cont_closed provenanceUnary localNameUnary provenanceLocalPkg
  have nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed pkgReadUnary routeUnary pkgRouteName
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row provenance ∨ hsame row localName ∨ hsame row pkgRead ∨
              hsame row nameRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont provenance localName pkgRead ∧
              Cont pkgRead route nameRead ∧ PkgSig bundle pkgRead pkg ∧
                PkgSig bundle nameRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nameRead ⟨hsame_refl nameRead, nameReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, provenanceLocalPkg, pkgRouteName, pkgReadPkg, nameReadPkg⟩
  }
  exact ⟨cert, pkgReadUnary, nameReadUnary⟩

end BEDC.Derived.AxiomDependencyTupleUp
