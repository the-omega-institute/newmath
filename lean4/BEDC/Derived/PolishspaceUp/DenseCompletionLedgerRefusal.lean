import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
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

theorem PolishSpaceDenseCompletionLedger_refusal [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport route provenance localName
      denseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metric →
      UnaryHistory complete →
        UnaryHistory separable →
          UnaryHistory stream →
            UnaryHistory readback →
              UnaryHistory ledger →
                UnaryHistory transport →
                  Cont stream ledger readback →
                    Cont ledger transport route →
                      Cont route separable denseRead →
                        PkgSig bundle provenance pkg →
                          PkgSig bundle localName pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row denseRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row stream ∨ hsame row readback ∨
                                    hsame row ledger ∨ hsame row complete ∨
                                      hsame row separable ∨ hsame row denseRead)
                                (fun row : BHist =>
                                  hsame row denseRead ∧ PkgSig bundle provenance pkg ∧
                                    PkgSig bundle localName pkg)
                                hsame ∧
                              UnaryHistory denseRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro _metricUnary _completeUnary separableUnary streamUnary _readbackUnary ledgerUnary
    transportUnary streamLedgerReadback ledgerTransportRoute routeSeparableDense provenancePkg
    localNamePkg
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary transportUnary ledgerTransportRoute
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed routeUnary separableUnary routeSeparableDense
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row denseRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
              hsame row complete ∨ hsame row separable ∨ hsame row denseRead)
          (fun row : BHist =>
            hsame row denseRead ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro denseRead ⟨hsame_refl denseRead, denseUnary⟩
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
      exact ⟨source.left, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, denseUnary⟩

end BEDC.Derived.PolishspaceUp
