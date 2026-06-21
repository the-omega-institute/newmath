import BEDC.Derived.DiagonallimitcompatibilityUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityPacketNameCertObligations [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance
      cert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row cert ∧
              DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback
                realSeal transport route provenance cert bundle pkg)
          (fun row : BHist =>
            hsame row diagonal ∨ hsame row triangle ∨ hsame row sealRow ∨
              hsame row dyadic ∨ hsame row windows ∨ hsame row readback ∨
                hsame row realSeal ∨ hsame row transport ∨ hsame row route ∨
                  hsame row provenance ∨ hsame row cert)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont diagonal triangle sealRow ∧ Cont dyadic windows readback ∧
              Cont readback realSeal route ∧ Cont route cert transport ∧
                PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory sealRow ∧
          UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
            UnaryHistory realSeal ∧ UnaryHistory transport ∧ UnaryHistory route ∧
              UnaryHistory provenance ∧ UnaryHistory cert := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier
  have carrierWitness :
      DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback
        realSeal transport route provenance cert bundle pkg := carrier
  obtain ⟨diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary, readbackUnary,
    realSealUnary, transportUnary, routeUnary, provenanceUnary, certUnary,
    diagonalTriangleSeal, dyadicWindowsReadback, readbackRealSealRoute, routeCertTransport,
    provenancePkg⟩ := carrier
  have certObject :
      SemanticNameCert
          (fun row : BHist =>
            hsame row cert ∧
              DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback
                realSeal transport route provenance cert bundle pkg)
          (fun row : BHist =>
            hsame row diagonal ∨ hsame row triangle ∨ hsame row sealRow ∨
              hsame row dyadic ∨ hsame row windows ∨ hsame row readback ∨
                hsame row realSeal ∨ hsame row transport ∨ hsame row route ∨
                  hsame row provenance ∨ hsame row cert)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont diagonal triangle sealRow ∧ Cont dyadic windows readback ∧
              Cont readback realSeal route ∧ Cont route cert transport ∧
                PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro cert
        (And.intro (hsame_refl cert) carrierWitness)
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
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
    }
    pattern_sound := by
      intro _row source
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      have rowUnary : UnaryHistory _ := unary_transport certUnary (hsame_symm source.left)
      exact
        ⟨rowUnary, diagonalTriangleSeal, dyadicWindowsReadback, readbackRealSealRoute,
          routeCertTransport, provenancePkg⟩
  }
  exact
    ⟨certObject, diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary,
      readbackUnary, realSealUnary, transportUnary, routeUnary, provenanceUnary, certUnary⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
