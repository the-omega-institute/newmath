import BEDC.Derived.CalculusUp.RootUnblockRegSeqRatRealSealFactorization

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusContinuityRealReadbackObligation [AskSetup] [PackageSetup]
    {R L C D I Q H T P N continuityRead readbackRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CalculusCarrier R L C D I Q H T P N bundle pkg →
      Cont C L continuityRead →
        Cont continuityRead Q readbackRead →
          Cont readbackRead R realRead →
            PkgSig bundle realRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row C ∨ hsame row L ∨ hsame row Q ∨ hsame row R ∨
                      hsame row realRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont C L continuityRead ∧
                      Cont continuityRead Q readbackRead ∧ Cont readbackRead R realRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle realRead pkg)
                  hsame ∧
                UnaryHistory continuityRead ∧ UnaryHistory readbackRead ∧
                  UnaryHistory realRead := by
  -- BEDC touchpoint anchor: CalculusCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrierRows continuityRoute readbackRoute realRoute realPkg
  obtain ⟨realUnary, limitUnary, continuousUnary, _derivativeUnary, _integralUnary,
    readbackUnary, _transportUnary, _replayUnary, _provenanceUnary, _localCertUnary,
    _realLimitContinuous, _continuousDerivativeIntegral, _derivativeReadbackTransports,
    _transportsReplayLocalCert, provenancePkg⟩ := carrierRows
  have continuityUnary : UnaryHistory continuityRead :=
    unary_cont_closed continuousUnary limitUnary continuityRoute
  have finalReadbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed continuityUnary readbackUnary readbackRoute
  have finalRealUnary : UnaryHistory realRead :=
    unary_cont_closed finalReadbackUnary realUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row L ∨ hsame row Q ∨ hsame row R ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C L continuityRead ∧
              Cont continuityRead Q readbackRead ∧ Cont readbackRead R realRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle realRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, finalRealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, continuityRoute, readbackRoute, realRoute, provenancePkg,
          realPkg⟩
  }
  exact ⟨cert, continuityUnary, finalReadbackUnary, finalRealUnary⟩

end BEDC.Derived.CalculusUp
