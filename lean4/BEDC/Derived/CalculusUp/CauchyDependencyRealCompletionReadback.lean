import BEDC.Derived.CalculusUp

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusCauchyDependencyRealCompletionReadback [AskSetup] [PackageSetup]
    {real limit continuous derivative integral readback transport replay provenance localName
      derivativeRead integralRead cauchyWindow realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CalculusRootDerivativeIntegralCarrier real limit continuous derivative integral readback
        transport replay provenance localName bundle pkg →
      Cont continuous derivative derivativeRead →
        Cont integral readback integralRead →
          Cont derivativeRead integralRead cauchyWindow →
            Cont cauchyWindow real realSeal →
              PkgSig bundle provenance pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row readback ∨ hsame row cauchyWindow ∨
                        hsame row realSeal ∨ hsame row real)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont derivativeRead integralRead cauchyWindow ∧
                        Cont cauchyWindow real realSeal ∧ PkgSig bundle provenance pkg)
                    hsame ∧
                  UnaryHistory cauchyWindow ∧ UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier derivativeRoute integralRoute cauchyRoute realSealRoute provenancePkg
  obtain ⟨realUnary, _limitUnary, continuousUnary, derivativeUnary, integralUnary,
    readbackUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _realLimitRoute, _continuousDerivativeIntegral, _derivativeTransportRoute,
    _transportReplayRoute, _carrierProvenancePkg⟩ := carrier
  have derivativeReadUnary : UnaryHistory derivativeRead :=
    unary_cont_closed continuousUnary derivativeUnary derivativeRoute
  have integralReadUnary : UnaryHistory integralRead :=
    unary_cont_closed integralUnary readbackUnary integralRoute
  have cauchyWindowUnary : UnaryHistory cauchyWindow :=
    unary_cont_closed derivativeReadUnary integralReadUnary cauchyRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed cauchyWindowUnary realUnary realSealRoute
  have sourceAtRealSeal :
      (fun row : BHist => hsame row realSeal ∧ UnaryHistory row) realSeal := by
    exact ⟨hsame_refl realSeal, realSealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row readback ∨ hsame row cauchyWindow ∨ hsame row realSeal ∨
              hsame row real)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont derivativeRead integralRead cauchyWindow ∧
              Cont cauchyWindow real realSeal ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal sourceAtRealSeal
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, cauchyRoute, realSealRoute, provenancePkg⟩
  }
  exact ⟨cert, cauchyWindowUnary, realSealUnary⟩

end BEDC.Derived.CalculusUp
