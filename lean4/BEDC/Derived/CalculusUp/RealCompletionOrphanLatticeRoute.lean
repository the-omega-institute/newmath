import BEDC.Derived.CalculusUp

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusRealCompletionOrphanLatticeRoute [AskSetup] [PackageSetup]
    {real limit continuous derivative integral readback transport replay provenance
      localName derivativeRead integralRead endpointRead finiteSeal publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CalculusRootDerivativeIntegralCarrier real limit continuous derivative integral readback
        transport replay provenance localName bundle pkg →
      Cont continuous derivative derivativeRead →
        Cont integral readback integralRead →
          Cont derivativeRead integralRead endpointRead →
            Cont endpointRead limit finiteSeal →
              Cont finiteSeal real publicRead →
                PkgSig bundle publicRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row derivativeRead ∨ hsame row integralRead ∨
                          hsame row endpointRead ∨ hsame row finiteSeal ∨
                            hsame row publicRead) ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row derivativeRead ∨ hsame row integralRead ∨
                          hsame row endpointRead ∨ hsame row finiteSeal ∨
                            hsame row publicRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont endpointRead limit finiteSeal ∧
                          Cont finiteSeal real publicRead ∧ PkgSig bundle publicRead pkg)
                      hsame ∧
                    UnaryHistory finiteSeal ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier derivativeRoute integralRoute endpointRoute finiteRoute publicRoute publicPkg
  obtain ⟨realUnary, limitUnary, continuousUnary, derivativeUnary, integralUnary,
    readbackUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _realLimitRoute, _continuousDerivativeRoute, _derivativeTransportRoute,
    _transportReplayRoute, _provenancePkg⟩ := carrier
  have derivativeReadUnary : UnaryHistory derivativeRead :=
    unary_cont_closed continuousUnary derivativeUnary derivativeRoute
  have integralReadUnary : UnaryHistory integralRead :=
    unary_cont_closed integralUnary readbackUnary integralRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed derivativeReadUnary integralReadUnary endpointRoute
  have finiteSealUnary : UnaryHistory finiteSeal :=
    unary_cont_closed endpointReadUnary limitUnary finiteRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed finiteSealUnary realUnary publicRoute
  have publicSource :
      (fun row : BHist =>
        (hsame row derivativeRead ∨ hsame row integralRead ∨ hsame row endpointRead ∨
          hsame row finiteSeal ∨ hsame row publicRead) ∧ UnaryHistory row) publicRead :=
    ⟨Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl publicRead)))), publicReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row derivativeRead ∨ hsame row integralRead ∨ hsame row endpointRead ∨
              hsame row finiteSeal ∨ hsame row publicRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row derivativeRead ∨ hsame row integralRead ∨ hsame row endpointRead ∨
              hsame row finiteSeal ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont endpointRead limit finiteSeal ∧
              Cont finiteSeal real publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead publicSource
      equiv_refl := by intro row _source; exact hsame_refl row
      equiv_symm := by intro _row _other sameRows; exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by intro _row source; exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, finiteRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, finiteSealUnary, publicReadUnary⟩

end BEDC.Derived.CalculusUp
