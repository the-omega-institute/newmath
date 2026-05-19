import BEDC.Derived.RegSeqRatUp

namespace BEDC.Derived.RegSeqRatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegSeqRatRealSealRouteExclusionPackage [AskSetup] [PackageSetup]
    {schedule index endpoint radius regularity provenance readback endpoint' regularity' sealRead
      terminal : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance readback bundle pkg ->
      hsame endpoint endpoint' ->
        Cont endpoint' radius regularity' ->
          Cont regularity' provenance sealRead ->
            Cont sealRead readback terminal ->
              PkgSig bundle sealRead pkg ->
                PkgSig bundle terminal pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row schedule ∨ hsame row endpoint' ∨ hsame row regularity' ∨
                          hsame row sealRead ∨ hsame row terminal)
                      (fun row : BHist => hsame row terminal ∧ PkgSig bundle terminal pkg)
                      hsame ∧
                    RegSeqRatStreamCarrier schedule index endpoint' radius regularity' provenance
                      sealRead bundle pkg ∧
                      hsame regularity regularity' ∧ hsame readback sealRead ∧
                        UnaryHistory terminal ∧ Cont sealRead readback terminal ∧
                          PkgSig bundle sealRead pkg ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier sameEndpoint endpointRadiusRegularity regularityProvenanceSealRead
    sealReadReadbackTerminal sealReadPkg terminalPkg
  have handoff :
      RegSeqRatStreamCarrier schedule index endpoint' radius regularity' provenance sealRead
          bundle pkg ∧
        hsame regularity regularity' ∧ hsame readback sealRead :=
    RegSeqRatStreamCarrier_real_seal_handoff carrier sameEndpoint endpointRadiusRegularity
      regularityProvenanceSealRead sealReadPkg
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed handoff.left.right.right.right.right.right.right.left
      carrier.right.right.right.right.right.right.left sealReadReadbackTerminal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row schedule ∨ hsame row endpoint' ∨ hsame row regularity' ∨
              hsame row sealRead ∨ hsame row terminal)
          (fun row : BHist => hsame row terminal ∧ PkgSig bundle terminal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminal
        ⟨hsame_refl terminal, terminalUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, terminalPkg⟩
  }
  exact
    ⟨cert, handoff.left, handoff.right.left, handoff.right.right, terminalUnary,
      sealReadReadbackTerminal, sealReadPkg, terminalPkg⟩

end BEDC.Derived.RegSeqRatUp
