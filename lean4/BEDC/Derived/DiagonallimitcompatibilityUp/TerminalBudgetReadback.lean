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

theorem DiagonalLimitCompatibilityCarrier_terminal_budget_readback
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetPrefix budgetWindow budgetRead terminalRead envelopeRead refinementRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal dyadic budgetPrefix →
        Cont budgetPrefix windows budgetWindow →
          Cont budgetWindow readback budgetRead →
            Cont budgetRead realSeal terminalRead →
              Cont terminalRead route envelopeRead →
                Cont terminalRead cert refinementRead →
                  PkgSig bundle terminalRead pkg →
                    PkgSig bundle envelopeRead pkg →
                      PkgSig bundle refinementRead pkg →
                        UnaryHistory budgetPrefix ∧ UnaryHistory budgetWindow ∧
                          UnaryHistory budgetRead ∧ UnaryHistory terminalRead ∧
                            UnaryHistory envelopeRead ∧ UnaryHistory refinementRead ∧
                              Cont diagonal dyadic budgetPrefix ∧
                                Cont budgetPrefix windows budgetWindow ∧
                                  Cont budgetWindow readback budgetRead ∧
                                    Cont budgetRead realSeal terminalRead ∧
                                      Cont terminalRead route envelopeRead ∧
                                        Cont terminalRead cert refinementRead ∧
                                          PkgSig bundle provenance pkg ∧
                                            PkgSig bundle terminalRead pkg ∧
                                              PkgSig bundle envelopeRead pkg ∧
                                                PkgSig bundle refinementRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier diagonalDyadicPrefix prefixWindowsBudget budgetWindowRead
    budgetRealTerminal terminalRouteEnvelope terminalCertRefinement terminalPkg envelopePkg
    refinementPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, routeUnary, _provenanceUnary, certUnary,
    _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetPrefixUnary : UnaryHistory budgetPrefix :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicPrefix
  have budgetWindowUnary : UnaryHistory budgetWindow :=
    unary_cont_closed budgetPrefixUnary windowsUnary prefixWindowsBudget
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed budgetWindowUnary readbackUnary budgetWindowRead
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed budgetReadUnary realSealUnary budgetRealTerminal
  have envelopeReadUnary : UnaryHistory envelopeRead :=
    unary_cont_closed terminalReadUnary routeUnary terminalRouteEnvelope
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed terminalReadUnary certUnary terminalCertRefinement
  exact
    ⟨budgetPrefixUnary, budgetWindowUnary, budgetReadUnary, terminalReadUnary,
      envelopeReadUnary, refinementReadUnary, diagonalDyadicPrefix, prefixWindowsBudget,
      budgetWindowRead, budgetRealTerminal, terminalRouteEnvelope, terminalCertRefinement,
      provenancePkg, terminalPkg, envelopePkg, refinementPkg⟩

theorem DiagonalLimitCompatibility_terminal_route_semantic_certificate
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetPrefix budgetWindow budgetRead terminalRead envelopeRead refinementRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic budgetPrefix ->
        Cont budgetPrefix windows budgetWindow ->
          Cont budgetWindow readback budgetRead ->
            Cont budgetRead realSeal terminalRead ->
              Cont terminalRead route envelopeRead ->
                Cont terminalRead cert refinementRead ->
                  PkgSig bundle terminalRead pkg ->
                    PkgSig bundle envelopeRead pkg ->
                      PkgSig bundle refinementRead pkg ->
                        SemanticNameCert
                          (fun row : BHist =>
                            hsame row terminalRead ∨ hsame row envelopeRead ∨
                              hsame row refinementRead)
                          (fun row : BHist =>
                            (hsame row terminalRead ∨ hsame row envelopeRead ∨
                              hsame row refinementRead) ∧ UnaryHistory row)
                          (fun row : BHist =>
                            (hsame row terminalRead ∨ hsame row envelopeRead ∨
                              hsame row refinementRead) ∧ PkgSig bundle provenance pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier diagonalDyadicPrefix prefixWindowsBudget budgetWindowRead
    budgetRealTerminal terminalRouteEnvelope terminalCertRefinement _terminalPkg _envelopePkg
    _refinementPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, routeUnary, _provenanceUnary, certUnary,
    _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetPrefixUnary : UnaryHistory budgetPrefix :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicPrefix
  have budgetWindowUnary : UnaryHistory budgetWindow :=
    unary_cont_closed budgetPrefixUnary windowsUnary prefixWindowsBudget
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed budgetWindowUnary readbackUnary budgetWindowRead
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed budgetReadUnary realSealUnary budgetRealTerminal
  have envelopeReadUnary : UnaryHistory envelopeRead :=
    unary_cont_closed terminalReadUnary routeUnary terminalRouteEnvelope
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed terminalReadUnary certUnary terminalCertRefinement
  exact {
    core := {
      carrier_inhabited := Exists.intro terminalRead (Or.inl (hsame_refl terminalRead))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same source
        cases source with
        | inl rowTerminal =>
            exact Or.inl (hsame_trans (hsame_symm same) rowTerminal)
        | inr tail =>
            cases tail with
            | inl rowEnvelope =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm same) rowEnvelope))
            | inr rowRefinement =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm same) rowRefinement))
    }
    pattern_sound := by
      intro row source
      cases source with
      | inl rowTerminal =>
          exact ⟨Or.inl rowTerminal, unary_transport terminalReadUnary (hsame_symm rowTerminal)⟩
      | inr tail =>
          cases tail with
          | inl rowEnvelope =>
              exact
                ⟨Or.inr (Or.inl rowEnvelope),
                  unary_transport envelopeReadUnary (hsame_symm rowEnvelope)⟩
          | inr rowRefinement =>
              exact
                ⟨Or.inr (Or.inr rowRefinement),
                  unary_transport refinementReadUnary (hsame_symm rowRefinement)⟩
    ledger_sound := by
      intro _row source
      exact ⟨source, provenancePkg⟩
  }

end BEDC.Derived.DiagonallimitcompatibilityUp
