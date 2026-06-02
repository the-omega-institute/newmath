import BEDC.Derived.PolishspaceUp.CompleteSeparableSynthesis

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceObservationLedgerConsumerExactness [AskSetup] [PackageSetup]
    {M K D S R W H C G N completionRead denseRead synthesisRead ledgerRoute
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.PolishSpaceUp.PolishSpaceCarrier M K D S R W H C G N bundle pkg →
      Cont M K completionRead →
        Cont M D denseRead →
          Cont completionRead denseRead synthesisRead →
            Cont W synthesisRead ledgerRoute →
              Cont W ledgerRoute consumerRead →
                PkgSig bundle synthesisRead pkg →
                  PkgSig bundle consumerRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row S ∨
                            hsame row R ∨ hsame row W ∨ hsame row synthesisRead ∨
                              hsame row ledgerRoute ∨ hsame row consumerRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle G pkg ∧
                            PkgSig bundle consumerRead pkg)
                        hsame ∧
                      UnaryHistory completionRead ∧ UnaryHistory denseRead ∧
                        UnaryHistory synthesisRead ∧ UnaryHistory ledgerRoute ∧
                          UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier completionRoute denseRoute synthesisRoute ledgerRouteCont consumerRoute
    _synthesisPkg consumerPkg
  obtain ⟨MUnary, KUnary, DUnary, _SUnary, _RUnary, WUnary, _HUnary, _CUnary,
    _GUnary, _NUnary, _metricCompleteLedger, _ledgerStreamReadback,
    _transportReplayProvenance, carrierPkg, _localPkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed MUnary KUnary completionRoute
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed MUnary DUnary denseRoute
  have synthesisUnary : UnaryHistory synthesisRead :=
    unary_cont_closed completionUnary denseUnary synthesisRoute
  have ledgerUnary : UnaryHistory ledgerRoute :=
    unary_cont_closed WUnary synthesisUnary ledgerRouteCont
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed WUnary ledgerUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨
              hsame row W ∨ hsame row synthesisRead ∨ hsame row ledgerRoute ∨
                hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle G pkg ∧ PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
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
                    (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, carrierPkg, consumerPkg⟩
  }
  exact ⟨cert, completionUnary, denseUnary, synthesisUnary, ledgerUnary, consumerUnary⟩

end BEDC.Derived.PolishspaceUp
