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

def CauchyOscillationPacket [AskSetup] [PackageSetup]
    (tailWindow modulus tolerance oscillation sealRow transport routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory tailWindow ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
    UnaryHistory oscillation ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont tailWindow modulus tolerance ∧ Cont tolerance oscillation sealRow ∧
          Cont sealRow transport routes ∧ Cont routes provenance name ∧ PkgSig bundle name pkg

theorem CauchyOscillationPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {tailWindow modulus tolerance oscillation sealRow transport routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationPacket tailWindow modulus tolerance oscillation sealRow transport routes
        provenance name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyOscillationPacket tailWindow modulus tolerance oscillation sealRow transport routes
              provenance name bundle pkg ∧
            hsame row name)
        (fun row : BHist =>
          CauchyOscillationPacket tailWindow modulus tolerance oscillation sealRow transport routes
              provenance name bundle pkg ∧
            hsame row name)
        (fun row : BHist =>
          CauchyOscillationPacket tailWindow modulus tolerance oscillation sealRow transport routes
              provenance name bundle pkg ∧
            hsame row name)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro name (And.intro packet (hsame_refl name))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.CauchyOscillationUp
