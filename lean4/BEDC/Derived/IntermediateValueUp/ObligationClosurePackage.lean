import BEDC.Derived.IntermediateValueUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.IntermediateValueUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem IntermediateValueCarrier_obligation_closure_package [AskSetup] [PackageSetup]
    {locatedInterval endpointNegative endpointPositive continuousMap modulusBudget
      bisectionLedger nestedWindow realSeal transports routes provenance localNameCert
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntermediateValueCarrier locatedInterval endpointNegative endpointPositive continuousMap
        modulusBudget bisectionLedger nestedWindow realSeal transports routes provenance
        localNameCert bundle pkg ->
      Cont nestedWindow realSeal consumerRead ->
        PkgSig bundle consumerRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row locatedInterval ∨ hsame row bisectionLedger ∨
                  hsame row nestedWindow ∨ hsame row realSeal ∨ hsame row consumerRead)
              (fun row : BHist =>
                hsame row locatedInterval ∨ hsame row bisectionLedger ∨
                  hsame row nestedWindow ∨ hsame row realSeal ∨ hsame row consumerRead)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg ∧
                  (hsame row locatedInterval ∨ hsame row bisectionLedger ∨
                    hsame row nestedWindow ∨ hsame row realSeal ∨ hsame row consumerRead))
              hsame ∧
            UnaryHistory nestedWindow ∧ UnaryHistory realSeal ∧ UnaryHistory consumerRead ∧
              Cont modulusBudget bisectionLedger nestedWindow ∧
                Cont bisectionLedger nestedWindow realSeal ∧
                  Cont nestedWindow realSeal consumerRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier nestedSealConsumer consumerPkg
  obtain ⟨_locatedUnary, _endpointNegativeUnary, _endpointPositiveUnary, _continuousUnary,
    modulusUnary, bisectionUnary, _transportsUnary, _routesUnary, _provenanceUnary,
    _localNameCertUnary, modulusBisectionNested, bisectionNestedReal, provenancePkg,
    _localNameCertPkg⟩ := carrier
  have nestedUnary : UnaryHistory nestedWindow :=
    unary_cont_closed modulusUnary bisectionUnary modulusBisectionNested
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed bisectionUnary nestedUnary bisectionNestedReal
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed nestedUnary realSealUnary nestedSealConsumer
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row locatedInterval ∨ hsame row bisectionLedger ∨
              hsame row nestedWindow ∨ hsame row realSeal ∨ hsame row consumerRead)
          (fun row : BHist =>
            hsame row locatedInterval ∨ hsame row bisectionLedger ∨
              hsame row nestedWindow ∨ hsame row realSeal ∨ hsame row consumerRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg ∧
              (hsame row locatedInterval ∨ hsame row bisectionLedger ∨
                hsame row nestedWindow ∨ hsame row realSeal ∨ hsame row consumerRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro locatedInterval (Or.inl (hsame_refl locatedInterval))
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
        cases source with
        | inl sameLocated =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameLocated)
        | inr rest =>
            cases rest with
            | inl sameBisection =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameBisection))
            | inr rest =>
                cases rest with
                | inl sameNested =>
                    exact
                      Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameNested)))
                | inr rest =>
                    cases rest with
                    | inl sameReal =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameReal))))
                    | inr sameConsumer =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (hsame_trans (hsame_symm sameRows) sameConsumer))))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, consumerPkg, source⟩
  }
  exact
    ⟨cert, nestedUnary, realSealUnary, consumerUnary, modulusBisectionNested,
      bisectionNestedReal, nestedSealConsumer, provenancePkg, consumerPkg⟩

end BEDC.Derived.IntermediateValueUp
