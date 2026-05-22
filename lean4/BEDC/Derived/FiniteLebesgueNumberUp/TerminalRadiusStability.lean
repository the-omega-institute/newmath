import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberPhaseRealTerminalRadiusStability [AskSetup]
    [PackageSetup]
    {cover window radius mesh transport route provenance nameRow terminalRead compactRead
      compactNetRead continuousRead uniformRead terminalRead' compactRead' compactNetRead'
      continuousRead' uniformRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont route nameRow terminalRead →
        Cont terminalRead radius compactRead →
          Cont compactRead mesh compactNetRead →
            Cont compactNetRead route continuousRead →
              Cont continuousRead nameRow uniformRead →
                hsame terminalRead' terminalRead →
                  hsame compactRead' compactRead →
                    hsame compactNetRead' compactNetRead →
                      hsame continuousRead' continuousRead →
                        hsame uniformRead' uniformRead →
                          PkgSig bundle uniformRead pkg →
                            UnaryHistory terminalRead' ∧ UnaryHistory compactRead' ∧
                              UnaryHistory compactNetRead' ∧ UnaryHistory continuousRead' ∧
                                UnaryHistory uniformRead' ∧
                                  SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row uniformRead' ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row terminalRead' ∨ hsame row compactRead' ∨
                                        hsame row compactNetRead' ∨
                                          hsame row continuousRead' ∨
                                            hsame row uniformRead')
                                    (fun row : BHist =>
                                      hsame row uniformRead' ∧
                                        PkgSig bundle uniformRead pkg)
                                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier routeNameTerminal terminalRadiusCompact compactMeshCompactNet
    compactNetRouteContinuous continuousNameUniform sameTerminal sameCompact sameCompactNet
    sameContinuous sameUniform uniformPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameTerminal
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed terminalUnary radiusUnary terminalRadiusCompact
  have compactNetUnary : UnaryHistory compactNetRead :=
    unary_cont_closed compactUnary meshUnary compactMeshCompactNet
  have continuousUnary : UnaryHistory continuousRead :=
    unary_cont_closed compactNetUnary routeUnary compactNetRouteContinuous
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed continuousUnary nameRowUnary continuousNameUniform
  have terminalPrimeUnary : UnaryHistory terminalRead' :=
    unary_transport terminalUnary (hsame_symm sameTerminal)
  have compactPrimeUnary : UnaryHistory compactRead' :=
    unary_transport compactUnary (hsame_symm sameCompact)
  have compactNetPrimeUnary : UnaryHistory compactNetRead' :=
    unary_transport compactNetUnary (hsame_symm sameCompactNet)
  have continuousPrimeUnary : UnaryHistory continuousRead' :=
    unary_transport continuousUnary (hsame_symm sameContinuous)
  have uniformPrimeUnary : UnaryHistory uniformRead' :=
    unary_transport uniformUnary (hsame_symm sameUniform)
  have sourceUniform :
      (fun row : BHist => hsame row uniformRead' ∧ UnaryHistory row) uniformRead' := by
    exact ⟨hsame_refl uniformRead', uniformPrimeUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row uniformRead' ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row terminalRead' ∨ hsame row compactRead' ∨
            hsame row compactNetRead' ∨ hsame row continuousRead' ∨
              hsame row uniformRead')
        (fun row : BHist => hsame row uniformRead' ∧ PkgSig bundle uniformRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro uniformRead' sourceUniform
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
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, uniformPkg⟩
    }
  exact
    ⟨terminalPrimeUnary, compactPrimeUnary, compactNetPrimeUnary, continuousPrimeUnary,
      uniformPrimeUnary, cert⟩

end BEDC.Derived.FiniteLebesgueNumberUp
