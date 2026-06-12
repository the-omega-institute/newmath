import BEDC.Derived.ParsevalUp.NameCertObligations

namespace BEDC.Derived.ParsevalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ParsevalFourierEnergyWindow [AskSetup] [PackageSetup]
    {F S I E R D L H C P N coefficientRead energyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ParsevalCarrierSurface F S I E R D L H C P N bundle pkg →
      Cont F S coefficientRead →
        Cont coefficientRead I energyRead →
          PkgSig bundle energyRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row F ∨ hsame row S ∨ hsame row I ∨
                    hsame row coefficientRead ∨ hsame row energyRead)
                (fun row : BHist => UnaryHistory row)
                (fun _row : BHist => PkgSig bundle P pkg ∧ PkgSig bundle energyRead pkg)
                hsame ∧
              UnaryHistory coefficientRead ∧ UnaryHistory energyRead := by
  -- BEDC touchpoint anchor: ParsevalCarrierSurface BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coefficientRoute energyRoute energyPkg
  obtain ⟨fourierUnary, sourceUnary, pairingUnary, _integralUnary, _readbackUnary,
    _toleranceUnary, _sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, provenancePkg, _localNamePkg⟩ := carrier
  have coefficientUnary : UnaryHistory coefficientRead :=
    unary_cont_closed fourierUnary sourceUnary coefficientRoute
  have energyUnary : UnaryHistory energyRead :=
    unary_cont_closed coefficientUnary pairingUnary energyRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row F ∨ hsame row S ∨ hsame row I ∨ hsame row coefficientRead ∨
              hsame row energyRead)
          (fun row : BHist => UnaryHistory row)
          (fun _row : BHist => PkgSig bundle P pkg ∧ PkgSig bundle energyRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro F (Or.inl (hsame_refl F))
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
        cases source with
        | inl fourierSource =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) fourierSource)
        | inr rest =>
            cases rest with
            | inl sourceRow =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sourceRow))
            | inr rest =>
                cases rest with
                | inl pairingSource =>
                    exact
                      Or.inr
                        (Or.inr
                          (Or.inl (hsame_trans (hsame_symm sameRows) pairingSource)))
                | inr rest =>
                    cases rest with
                    | inl coefficientSource =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl
                                  (hsame_trans (hsame_symm sameRows) coefficientSource))))
                    | inr energySource =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (hsame_trans (hsame_symm sameRows) energySource))))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl fourierSource =>
          exact unary_transport fourierUnary (hsame_symm fourierSource)
      | inr rest =>
          cases rest with
          | inl sourceRow =>
              exact unary_transport sourceUnary (hsame_symm sourceRow)
          | inr rest =>
              cases rest with
              | inl pairingSource =>
                  exact unary_transport pairingUnary (hsame_symm pairingSource)
              | inr rest =>
                  cases rest with
                  | inl coefficientSource =>
                      exact unary_transport coefficientUnary (hsame_symm coefficientSource)
                  | inr energySource =>
                      exact unary_transport energyUnary (hsame_symm energySource)
    ledger_sound := by
      intro _row _source
      exact ⟨provenancePkg, energyPkg⟩
  }
  exact ⟨cert, coefficientUnary, energyUnary⟩

end BEDC.Derived.ParsevalUp
