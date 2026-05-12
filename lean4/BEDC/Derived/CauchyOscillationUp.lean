import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyOscillationCarrier [AskSetup] [PackageSetup]
    (tailWindow modulus tolerance ledger «seal» transport routes provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory tailWindow ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
    UnaryHistory ledger ∧ UnaryHistory «seal» ∧ UnaryHistory transport ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory nameCert ∧
        Cont tailWindow modulus tolerance ∧ Cont modulus tolerance ledger ∧
          Cont ledger «seal» routes ∧ Cont routes nameCert provenance ∧
            PkgSig bundle provenance pkg

theorem CauchyOscillationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {tailWindow modulus tolerance ledger sealRow transport routes provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes provenance
        nameCert bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row provenance ∧
              CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes
                provenance nameCert bundle pkg)
          (fun row : BHist => hsame row provenance ∧ Cont tailWindow modulus tolerance)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory tailWindow ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
          UnaryHistory ledger ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
            UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory nameCert ∧
              Cont tailWindow modulus tolerance ∧ Cont modulus tolerance ledger ∧
                Cont ledger sealRow routes ∧ Cont routes nameCert provenance ∧
                  PkgSig bundle provenance pkg := by
  intro carrier
  obtain ⟨tailWindowUnary, modulusUnary, toleranceUnary, ledgerUnary, sealUnary,
    transportUnary, routesUnary, provenanceUnary, nameCertUnary, tailWindowModulus,
    modulusTolerance, ledgerSeal, routesNameCert, provenancePkg⟩ := carrier
  have carrierRows :
      CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes
        provenance nameCert bundle pkg :=
    ⟨tailWindowUnary, modulusUnary, toleranceUnary, ledgerUnary, sealUnary, transportUnary,
      routesUnary, provenanceUnary, nameCertUnary, tailWindowModulus, modulusTolerance,
      ledgerSeal, routesNameCert, provenancePkg⟩
  have sourceProvenance :
      (fun row : BHist =>
        hsame row provenance ∧
          CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes
            provenance nameCert bundle pkg) provenance := by
    exact ⟨hsame_refl provenance, carrierRows⟩
  have core :
      NameCert
        (fun row : BHist =>
          hsame row provenance ∧
            CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes
              provenance nameCert bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro provenance sourceProvenance
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other same
        exact hsame_symm same
      equiv_trans := by
        intro row other third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro row other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row provenance ∧
              CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes
                provenance nameCert bundle pkg)
          (fun row : BHist => hsame row provenance ∧ Cont tailWindow modulus tolerance)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro row source
        exact ⟨source.left, tailWindowModulus⟩
      ledger_sound := by
        intro row source
        exact ⟨source.left, provenancePkg⟩
    }
  exact
    ⟨cert, tailWindowUnary, modulusUnary, toleranceUnary, ledgerUnary, sealUnary,
      transportUnary, routesUnary, provenanceUnary, nameCertUnary, tailWindowModulus,
      modulusTolerance, ledgerSeal, routesNameCert, provenancePkg⟩

end BEDC.Derived.CauchyOscillationUp
