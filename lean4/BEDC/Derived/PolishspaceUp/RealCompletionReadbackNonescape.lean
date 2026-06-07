import BEDC.Derived.PolishspaceUp.CompletionDensityHandoff

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishspaceRealCompletionReadbackNonescape [AskSetup] [PackageSetup]
    {M K D S R W H C G N completionRead denseRead synthesisRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.PolishSpaceUp.PolishSpaceCarrier M K D S R W H C G N bundle pkg →
      Cont M K completionRead →
        Cont M D denseRead →
          Cont completionRead denseRead synthesisRead →
            Cont synthesisRead W sealRead →
              PkgSig bundle sealRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row S ∨
                        hsame row R ∨ hsame row W ∨ hsame row synthesisRead ∨
                          hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont synthesisRead W sealRead ∧
                        PkgSig bundle sealRead pkg)
                    hsame ∧
                  UnaryHistory completionRead ∧ UnaryHistory denseRead ∧
                    UnaryHistory synthesisRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: PolishSpaceCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier completionRoute denseRoute synthesisRoute sealRoute sealPkg
  obtain ⟨MUnary, KUnary, DUnary, _SUnary, _RUnary, WUnary, _HUnary, _CUnary,
    _GUnary, _NUnary, _metricCompleteLedger, _ledgerStreamReadback,
    _transportReplayProvenance, _carrierPkg, _localPkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed MUnary KUnary completionRoute
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed MUnary DUnary denseRoute
  have synthesisUnary : UnaryHistory synthesisRead :=
    unary_cont_closed completionUnary denseUnary synthesisRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed synthesisUnary WUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row S ∨
              hsame row R ∨ hsame row W ∨ hsame row synthesisRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont synthesisRead W sealRead ∧
              PkgSig bundle sealRead pkg)
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sealRoute, sealPkg⟩
  }
  exact ⟨cert, completionUnary, denseUnary, synthesisUnary, sealUnary⟩

end BEDC.Derived.PolishspaceUp
