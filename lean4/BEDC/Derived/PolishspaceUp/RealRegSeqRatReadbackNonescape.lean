import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceRealRegSeqRatReadbackNonescape [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport replay provenance localName
      denseRead streamWindow realRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metric ->
      UnaryHistory complete ->
        UnaryHistory separable ->
          UnaryHistory stream ->
            UnaryHistory readback ->
              UnaryHistory ledger ->
                UnaryHistory transport ->
                  UnaryHistory replay ->
                    Cont metric separable denseRead ->
                      Cont denseRead stream streamWindow ->
                        Cont streamWindow readback realRead ->
                          Cont realRead ledger finalRead ->
                            PkgSig bundle provenance pkg ->
                              PkgSig bundle localName pkg ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row stream ∨ hsame row readback ∨
                                        hsame row ledger ∨ hsame row finalRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont realRead ledger finalRead ∧
                                        PkgSig bundle provenance pkg ∧
                                          PkgSig bundle localName pkg)
                                    hsame ∧
                                  UnaryHistory denseRead ∧ UnaryHistory streamWindow ∧
                                    UnaryHistory realRead ∧ UnaryHistory finalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro metricUnary _completeUnary separableUnary streamUnary readbackUnary ledgerUnary
    _transportUnary _replayUnary metricSeparableDense denseStreamWindow
    streamWindowReadbackReal realLedgerFinal provenancePkg localNamePkg
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed metricUnary separableUnary metricSeparableDense
  have streamWindowUnary : UnaryHistory streamWindow :=
    unary_cont_closed denseUnary streamUnary denseStreamWindow
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed streamWindowUnary readbackUnary streamWindowReadbackReal
  have finalUnary : UnaryHistory finalRead :=
    unary_cont_closed realUnary ledgerUnary realLedgerFinal
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro finalRead ⟨hsame_refl finalRead, finalUnary⟩
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
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, realLedgerFinal, provenancePkg, localNamePkg⟩
    }
  · exact ⟨denseUnary, streamWindowUnary, realUnary, finalUnary⟩

end BEDC.Derived.PolishspaceUp
