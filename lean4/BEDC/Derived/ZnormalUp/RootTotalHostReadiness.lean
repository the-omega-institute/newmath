import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_total_host_readiness [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name hostRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont routes name hostRead ->
        PkgSig bundle hostRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                ZnormalPacket typed fuel terminal normal continuation transports routes provenance
                  name bundle pkg ∧ hsame row hostRead)
              (fun row : BHist =>
                hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨ hsame row normal ∨
                  hsame row continuation ∨ hsame row transports ∨ hsame row routes ∨
                    hsame row provenance ∨ hsame row name ∨ hsame row hostRead)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle hostRead pkg ∧
                  hsame row hostRead)
              hsame ∧
            UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminal ∧
              UnaryHistory normal ∧ UnaryHistory continuation ∧ UnaryHistory transports ∧
                UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
                  UnaryHistory hostRead ∧ Cont typed fuel terminal ∧
                    Cont terminal normal continuation ∧ Cont continuation transports routes ∧
                      Cont routes name hostRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle hostRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet routesNameHost hostReadPkg
  have packetWitness := packet
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, provenanceUnary, nameUnary, typedFuelTerminal,
    terminalNormalContinuation, continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have hostReadUnary : UnaryHistory hostRead :=
    unary_cont_closed routesUnary nameUnary routesNameHost
  have sourceHost :
      (fun row : BHist =>
        ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
          bundle pkg ∧ hsame row hostRead) hostRead := by
    exact ⟨packetWitness, hsame_refl hostRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
              bundle pkg ∧ hsame row hostRead)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨ hsame row normal ∨
              hsame row continuation ∨ hsame row transports ∨ hsame row routes ∨
                hsame row provenance ∨ hsame row name ∨ hsame row hostRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle hostRead pkg ∧
              hsame row hostRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro hostRead sourceHost
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _row' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _row' sameRows source
          exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.right))))))))
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, hostReadPkg, source.right⟩
    }
  exact
    ⟨cert, typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
      transportsUnary, routesUnary, provenanceUnary, nameUnary, hostReadUnary,
      typedFuelTerminal, terminalNormalContinuation, continuationTransportsRoutes,
      routesNameHost, provenancePkg, hostReadPkg⟩

end BEDC.Derived.ZnormalUp
