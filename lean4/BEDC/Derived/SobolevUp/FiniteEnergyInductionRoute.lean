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

theorem SobolevFiniteEnergyInductionRoute [AskSetup] [PackageSetup]
    {source weakGradient derivative integral norm energy transport replay provenance
      energyRead replayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier source weakGradient derivative integral norm energy transport replay
        provenance bundle pkg ->
      Cont energy norm energyRead ->
        Cont energyRead replay replayRead ->
          Cont replayRead provenance namedRead ->
            PkgSig bundle replay pkg ->
              PkgSig bundle provenance pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row energy ∨ hsame row norm ∨ hsame row energyRead ∨
                        hsame row replayRead ∨ hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont energy norm energyRead ∧
                        Cont energyRead replay replayRead ∧
                          Cont replayRead provenance namedRead ∧
                            PkgSig bundle replay pkg ∧ PkgSig bundle provenance pkg)
                    hsame ∧
                  UnaryHistory energyRead ∧ UnaryHistory replayRead ∧
                    UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier energyRoute replayRoute namedRoute replayPkg provenancePkg
  obtain ⟨_sourceUnary, _weakGradientUnary, _derivativeUnary, _integralUnary, normUnary,
    energyUnary, _transportUnary, replayUnary, provenanceUnary, _sourceWeakDerivative,
    _derivativeIntegralNorm, _normEnergyTransport, _transportReplayProvenance,
    _carrierPkg⟩ := carrier
  have energyReadUnary : UnaryHistory energyRead :=
    unary_cont_closed energyUnary normUnary energyRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed energyReadUnary replayUnary replayRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed replayReadUnary provenanceUnary namedRoute
  have sourceNamed :
      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row) namedRead := by
    exact ⟨hsame_refl namedRead, namedReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row energy ∨ hsame row norm ∨ hsame row energyRead ∨
              hsame row replayRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont energy norm energyRead ∧
              Cont energyRead replay replayRead ∧ Cont replayRead provenance namedRead ∧
                PkgSig bundle replay pkg ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead sourceNamed
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, energyRoute, replayRoute, namedRoute, replayPkg, provenancePkg⟩
  }
  exact ⟨cert, energyReadUnary, replayReadUnary, namedReadUnary⟩

end BEDC.Derived.SobolevUp
