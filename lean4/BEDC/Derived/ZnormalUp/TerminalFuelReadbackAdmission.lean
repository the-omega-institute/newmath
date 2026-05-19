import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_terminal_fuel_readback_admission [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      continuationRead downstream siblingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel terminalRead ->
        Cont terminalRead normal continuationRead ->
          Cont continuationRead transports downstream ->
            Cont normal continuation siblingRead ->
              PkgSig bundle downstream pkg ->
                PkgSig bundle siblingRead pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row downstream ∨ hsame row siblingRead) ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row terminalRead ∨ hsame row continuationRead ∨
                          hsame row downstream ∨ hsame row siblingRead)
                      (fun row : BHist =>
                        (hsame row downstream ∧ PkgSig bundle downstream pkg) ∨
                          (hsame row siblingRead ∧ PkgSig bundle siblingRead pkg))
                      hsame ∧
                    hsame terminalRead terminal ∧ UnaryHistory terminalRead ∧
                      UnaryHistory continuationRead ∧ UnaryHistory downstream ∧
                        UnaryHistory siblingRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelRead terminalReadNormalRead continuationReadTransportsDownstream
    normalContinuationSibling downstreamPkg siblingPkg
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have sameTerminalRead : hsame terminalRead terminal :=
    cont_deterministic typedFuelRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelRead
  have continuationReadUnary : UnaryHistory continuationRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed continuationReadUnary transportsUnary continuationReadTransportsDownstream
  have siblingReadUnary : UnaryHistory siblingRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationSibling
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro downstream
            (And.intro (Or.inl (hsame_refl downstream)) downstreamUnary)
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
          constructor
          · cases source.left with
            | inl sameDownstream =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameDownstream)
            | inr sameSibling =>
                exact Or.inr (hsame_trans (hsame_symm sameRows) sameSibling)
          · exact unary_transport source.right sameRows
      }
      pattern_sound := by
        intro row source
        cases source.left with
        | inl sameDownstream =>
            exact Or.inr (Or.inr (Or.inl sameDownstream))
        | inr sameSibling =>
            exact Or.inr (Or.inr (Or.inr sameSibling))
      ledger_sound := by
        intro row source
        cases source.left with
        | inl sameDownstream =>
            exact Or.inl (And.intro sameDownstream downstreamPkg)
        | inr sameSibling =>
            exact Or.inr (And.intro sameSibling siblingPkg)
    }
  · exact
      ⟨sameTerminalRead, terminalReadUnary, continuationReadUnary, downstreamUnary,
        siblingReadUnary, provenancePkg⟩

end BEDC.Derived.ZnormalUp
