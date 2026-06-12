import BEDC.Derived.CalculusUp.RootUnblockRegSeqRatRealSealFactorization

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusRootRegularReadbackObligation [AskSetup] [PackageSetup]
    {real limit continuous derivative integral readback transports replay provenance localCert
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CalculusCarrier real limit continuous derivative integral readback transports replay
        provenance localCert bundle pkg →
      Cont readback real sealRead →
        PkgSig bundle sealRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row limit ∨ hsame row derivative ∨ hsame row integral ∨
                  hsame row readback ∨ hsame row real ∨ hsame row sealRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont readback real sealRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg)
              hsame ∧
            UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: CalculusCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrierRows sealRoute sealPkg
  obtain ⟨realUnary, _limitUnary, _continuousUnary, _derivativeUnary, _integralUnary,
    readbackUnary, _transportsUnary, _replayUnary, _provenanceUnary, _localCertUnary,
    _realLimitContinuous, _continuousDerivativeIntegral, _derivativeReadbackTransports,
    _transportsReplayLocalCert, provenancePkg⟩ := carrierRows
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary realUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row limit ∨ hsame row derivative ∨ hsame row integral ∨
              hsame row readback ∨ hsame row real ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont readback real sealRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sealRoute, provenancePkg, sealPkg⟩
  }
  exact ⟨cert, sealUnary⟩

end BEDC.Derived.CalculusUp
