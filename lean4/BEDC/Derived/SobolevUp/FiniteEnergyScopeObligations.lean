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

theorem SobolevCarrier_compact_embedding_refusal_boundary [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert energyRead
      compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance localCert
        bundle pkg →
      Cont gradient routes energyRead →
        Cont energyRead localCert compactRead →
          PkgSig bundle provenance pkg →
            PkgSig bundle compactRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row domain ∨ hsame row base ∨ hsame row codomain ∨
                      hsame row magnitude ∨ hsame row gradient ∨ hsame row energyRead ∨
                        hsame row compactRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont gradient routes energyRead ∧
                      Cont energyRead localCert compactRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle compactRead pkg)
                  hsame ∧
                UnaryHistory energyRead ∧ UnaryHistory compactRead := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrierRows gradientRoutesEnergy energyLocalCompact provenancePkg compactPkg
  obtain ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary,
    _transportsUnary, routesUnary, _provenanceUnary, localCertUnary, _domainBaseCodomain,
    _codomainMagnitudeGradient, _gradientTransportsRoutes, _routesProvenanceLocalCert,
    _carrierProvenancePkg⟩ := carrierRows
  have energyUnary : UnaryHistory energyRead :=
    unary_cont_closed gradientUnary routesUnary gradientRoutesEnergy
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed energyUnary localCertUnary energyLocalCompact
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row domain ∨ hsame row base ∨ hsame row codomain ∨ hsame row magnitude ∨
              hsame row gradient ∨ hsame row energyRead ∨ hsame row compactRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont gradient routes energyRead ∧
              Cont energyRead localCert compactRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle compactRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro compactRead ⟨hsame_refl compactRead, compactUnary⟩
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
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, gradientRoutesEnergy, energyLocalCompact, provenancePkg, compactPkg⟩
  }
  exact ⟨cert, energyUnary, compactUnary⟩

theorem SobolevCarrier_finite_energy_obligation_scope [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert
      energyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance localCert
        bundle pkg →
      Cont (append (append domain magnitude) gradient) transports energyRead →
        PkgSig bundle energyRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row energyRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row domain ∨ hsame row base ∨ hsame row codomain ∨
                  hsame row magnitude ∨ hsame row gradient ∨ hsame row energyRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont domain base codomain ∧
                  Cont codomain magnitude gradient ∧ Cont gradient transports routes ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle energyRead pkg)
              hsame ∧
            UnaryHistory energyRead := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrierRows finiteEnergy energyPkg
  obtain ⟨domainUnary, _baseUnary, _codomainUnary, magnitudeUnary, gradientUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, gradientTransportsRoutes, _routesProvenanceLocalCert,
    provenancePkg⟩ := carrierRows
  have domainMagnitudeUnary : UnaryHistory (append domain magnitude) :=
    unary_append_closed domainUnary magnitudeUnary
  have domainMagnitudeGradientUnary :
      UnaryHistory (append (append domain magnitude) gradient) :=
    unary_append_closed domainMagnitudeUnary gradientUnary
  have energyUnary : UnaryHistory energyRead :=
    unary_cont_closed domainMagnitudeGradientUnary transportsUnary finiteEnergy
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row energyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row domain ∨ hsame row base ∨ hsame row codomain ∨ hsame row magnitude ∨
              hsame row gradient ∨ hsame row energyRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont domain base codomain ∧
              Cont codomain magnitude gradient ∧ Cont gradient transports routes ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle energyRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro energyRead ⟨hsame_refl energyRead, energyUnary⟩
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
      exact
        ⟨source.right, domainBaseCodomain, codomainMagnitudeGradient,
          gradientTransportsRoutes, provenancePkg, energyPkg⟩
  }
  exact ⟨cert, energyUnary⟩

end BEDC.Derived.SobolevUp
