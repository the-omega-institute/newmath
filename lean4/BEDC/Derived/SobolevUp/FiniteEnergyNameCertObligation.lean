import BEDC.Derived.SobolevUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_finite_energy_namecert_obligation [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert
      energyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg →
      hsame energyRead (append magnitude gradient) →
        SemanticNameCert
            (fun row : BHist => hsame row energyRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row magnitude ∨ hsame row gradient ∨ hsame row energyRead)
            (fun row : BHist =>
              UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                Cont codomain magnitude gradient)
            hsame ∧
          UnaryHistory energyRead ∧ UnaryHistory magnitude ∧ UnaryHistory gradient ∧
            Cont codomain magnitude gradient ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist hsame ProbeBundle Pkg Cont SemanticNameCert
  intro carrier sameEnergyRead
  obtain ⟨_domainUnary, _baseUnary, _codomainUnary, magnitudeUnary, gradientUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, _domainBaseCodomain,
    codomainMagnitudeGradient, _gradientTransportsRoutes, _routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have magnitudeGradientUnary : UnaryHistory (append magnitude gradient) :=
    unary_append_closed magnitudeUnary gradientUnary
  have energyReadUnary : UnaryHistory energyRead :=
    unary_transport magnitudeGradientUnary (hsame_symm sameEnergyRead)
  have sourceEnergy :
      (fun row : BHist => hsame row energyRead ∧ UnaryHistory row) energyRead := by
    exact ⟨hsame_refl energyRead, energyReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row energyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row magnitude ∨ hsame row gradient ∨ hsame row energyRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              Cont codomain magnitude gradient)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro energyRead sourceEnergy
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
      exact ⟨source.right, provenancePkg, codomainMagnitudeGradient⟩
  }
  exact
    ⟨cert, energyReadUnary, magnitudeUnary, gradientUnary, codomainMagnitudeGradient,
      provenancePkg⟩

end BEDC.Derived.SobolevUp
