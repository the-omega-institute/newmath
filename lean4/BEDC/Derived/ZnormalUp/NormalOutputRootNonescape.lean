import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_normal_output_root_nonescape [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name normalRead
      downstream output : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont normal continuation normalRead ->
        Cont normalRead transports downstream ->
          Cont downstream routes output ->
            PkgSig bundle output pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row output ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row normal ∨ hsame row continuation ∨ hsame row normalRead ∨
                      hsame row downstream ∨ hsame row output)
                  (fun row : BHist => hsame row output ∧ PkgSig bundle output pkg)
                  hsame ∧
                UnaryHistory terminal ∧ UnaryHistory normal ∧ UnaryHistory continuation ∧
                  UnaryHistory normalRead ∧ UnaryHistory downstream ∧ UnaryHistory output ∧
                    Cont terminal normal continuation ∧
                      Cont normal continuation normalRead ∧
                        Cont normalRead transports downstream ∧
                          Cont downstream routes output ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle output pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet normalContinuationRead normalReadTransportsDownstream
    downstreamRoutesOutput outputPkg
  obtain ⟨_typedUnary, _fuelUnary, terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed normalReadUnary transportsUnary normalReadTransportsDownstream
  have outputUnary : UnaryHistory output :=
    unary_cont_closed downstreamUnary routesUnary downstreamRoutesOutput
  have outputSource :
      (fun row : BHist => hsame row output ∧ UnaryHistory row) output := by
    exact ⟨hsame_refl output, outputUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row output ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row normal ∨ hsame row continuation ∨ hsame row normalRead ∨
              hsame row downstream ∨ hsame row output)
          (fun row : BHist => hsame row output ∧ PkgSig bundle output pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro output outputSource
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
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, outputPkg⟩
    }
  exact
    ⟨cert, terminalUnary, normalUnary, continuationUnary, normalReadUnary,
      downstreamUnary, outputUnary, terminalNormalContinuation, normalContinuationRead,
      normalReadTransportsDownstream, downstreamRoutesOutput, provenancePkg, outputPkg⟩

end BEDC.Derived.ZnormalUp
