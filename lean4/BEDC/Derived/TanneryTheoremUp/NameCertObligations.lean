import BEDC.Derived.TanneryTheoremUp
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.TanneryTheoremUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TanneryTheoremCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {array limit majorant windows readback dyadic endpoint transport route provenance cert :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TanneryTheoremCarrier array limit majorant windows readback dyadic endpoint transport route
        provenance cert bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧
              TanneryTheoremCarrier array limit majorant windows readback dyadic endpoint
                transport route provenance cert bundle pkg)
          (fun row : BHist =>
            hsame row endpoint ∧ UnaryHistory array ∧ UnaryHistory limit ∧
              UnaryHistory majorant ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                UnaryHistory dyadic)
          (fun row : BHist =>
            hsame row endpoint ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle cert pkg)
          hsame ∧
        UnaryHistory array ∧ UnaryHistory limit ∧ UnaryHistory majorant ∧
          UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory dyadic ∧
            UnaryHistory endpoint ∧ Cont array limit majorant ∧
              Cont majorant windows readback ∧ Cont readback dyadic endpoint ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrierWitness
  obtain ⟨arrayUnary, limitUnary, majorantUnary, windowsUnary, readbackUnary, dyadicUnary,
    endpointUnary, transportUnary, routeUnary, provenanceUnary, certUnary,
    arrayLimitMajorant, majorantWindowsReadback, readbackDyadicEndpoint,
    endpointTransportRoute, routeCertProvenance, provenancePkg, certPkg⟩ := carrierWitness
  have carrierRebuilt :
      TanneryTheoremCarrier array limit majorant windows readback dyadic endpoint transport route
        provenance cert bundle pkg :=
    ⟨arrayUnary, limitUnary, majorantUnary, windowsUnary, readbackUnary, dyadicUnary,
      endpointUnary, transportUnary, routeUnary, provenanceUnary, certUnary,
      arrayLimitMajorant, majorantWindowsReadback, readbackDyadicEndpoint,
      endpointTransportRoute, routeCertProvenance, provenancePkg, certPkg⟩
  have certObj :
      SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧
              TanneryTheoremCarrier array limit majorant windows readback dyadic endpoint
                transport route provenance cert bundle pkg)
          (fun row : BHist =>
            hsame row endpoint ∧ UnaryHistory array ∧ UnaryHistory limit ∧
              UnaryHistory majorant ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                UnaryHistory dyadic)
          (fun row : BHist =>
            hsame row endpoint ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle cert pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint ⟨hsame_refl endpoint, carrierRebuilt⟩
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨source.left, arrayUnary, limitUnary, majorantUnary, windowsUnary, readbackUnary,
          dyadicUnary⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, certPkg⟩
  }
  exact
    ⟨certObj, arrayUnary, limitUnary, majorantUnary, windowsUnary, readbackUnary, dyadicUnary,
      endpointUnary, arrayLimitMajorant, majorantWindowsReadback, readbackDyadicEndpoint,
      provenancePkg, certPkg⟩

end BEDC.Derived.TanneryTheoremUp
