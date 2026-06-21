import BEDC.Derived.CalculusUp.CauchyDependencyRoute

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusRealContinuousDependencyRoute [AskSetup] [PackageSetup]
    {real limit continuous derivative integral readback transport replay provenance localName
      functionRead scalarRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CalculusRootDerivativeIntegralCarrier real limit continuous derivative integral readback
        transport replay provenance localName bundle pkg ->
      Cont continuous real functionRead ->
        Cont functionRead replay scalarRead ->
          Cont scalarRead localName namedRead ->
            PkgSig bundle provenance pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row real ∨ hsame row continuous ∨ hsame row functionRead ∨
                      hsame row scalarRead ∨ hsame row replay ∨ hsame row localName ∨
                        hsame row namedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont continuous real functionRead ∧
                      Cont functionRead replay scalarRead ∧
                        Cont scalarRead localName namedRead ∧ PkgSig bundle provenance pkg)
                  hsame ∧
                UnaryHistory functionRead ∧ UnaryHistory scalarRead ∧
                  UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier functionRoute scalarRoute namedRoute provenancePkg
  obtain ⟨realUnary, _limitUnary, continuousUnary, _derivativeUnary, _integralUnary,
    _readbackUnary, _transportUnary, replayUnary, _provenanceUnary, localNameUnary,
    _realLimitRoute, _continuousDerivativeRoute, _derivativeTransportRoute,
    _transportReplayRoute, _carrierProvenancePkg⟩ := carrier
  have functionReadUnary : UnaryHistory functionRead :=
    unary_cont_closed continuousUnary realUnary functionRoute
  have scalarReadUnary : UnaryHistory scalarRead :=
    unary_cont_closed functionReadUnary replayUnary scalarRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed scalarReadUnary localNameUnary namedRoute
  have sourceNamed :
      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row) namedRead := by
    exact ⟨hsame_refl namedRead, namedReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row real ∨ hsame row continuous ∨ hsame row functionRead ∨
              hsame row scalarRead ∨ hsame row replay ∨ hsame row localName ∨
                hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont continuous real functionRead ∧
              Cont functionRead replay scalarRead ∧ Cont scalarRead localName namedRead ∧
                PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead sourceNamed
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, functionRoute, scalarRoute, namedRoute, provenancePkg⟩
  }
  exact ⟨cert, functionReadUnary, scalarReadUnary, namedReadUnary⟩

end BEDC.Derived.CalculusUp
