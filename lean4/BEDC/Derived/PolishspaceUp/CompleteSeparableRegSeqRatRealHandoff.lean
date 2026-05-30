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
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.FKernel.NameCert

theorem PolishSpaceCompleteSeparableRegSeqRatRealHandoff [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport replay completionRead denseRead
      sharedRead observationRead finalRead provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metric ->
      UnaryHistory complete ->
        UnaryHistory separable ->
          UnaryHistory stream ->
            UnaryHistory readback ->
              UnaryHistory ledger ->
                UnaryHistory transport ->
                  Cont metric complete completionRead ->
                    Cont metric separable denseRead ->
                      Cont completionRead denseRead sharedRead ->
                        Cont ledger transport replay ->
                          Cont replay readback observationRead ->
                            Cont observationRead sharedRead finalRead ->
                              PkgSig bundle provenance pkg ->
                                PkgSig bundle localName pkg ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row finalRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row metric ∨ hsame row complete ∨
                                          hsame row separable ∨ hsame row stream ∨
                                            hsame row readback ∨ hsame row sharedRead ∨
                                              hsame row finalRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                          PkgSig bundle localName pkg)
                                      hsame ∧
                                    UnaryHistory completionRead ∧ UnaryHistory denseRead ∧
                                      UnaryHistory sharedRead ∧ UnaryHistory observationRead ∧
                                        UnaryHistory finalRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert
  intro metricUnary completeUnary separableUnary _streamUnary readbackUnary ledgerUnary
    transportUnary metricComplete metricSeparable completeDenseShared ledgerTransport
    replayReadback observationShared provenancePkg localNamePkg
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed metricUnary completeUnary metricComplete
  have denseReadUnary : UnaryHistory denseRead :=
    unary_cont_closed metricUnary separableUnary metricSeparable
  have sharedReadUnary : UnaryHistory sharedRead :=
    unary_cont_closed completionReadUnary denseReadUnary completeDenseShared
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed ledgerUnary transportUnary ledgerTransport
  have observationReadUnary : UnaryHistory observationRead :=
    unary_cont_closed replayUnary readbackUnary replayReadback
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed observationReadUnary sharedReadUnary observationShared
  have sourceFinal :
      (fun row : BHist => hsame row finalRead ∧ UnaryHistory row) finalRead := by
    exact ⟨hsame_refl finalRead, finalReadUnary⟩
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro finalRead sourceFinal
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
        exact ⟨source.right, provenancePkg, localNamePkg⟩
    }
  · exact
      ⟨completionReadUnary, denseReadUnary, sharedReadUnary, observationReadUnary,
        finalReadUnary⟩

end BEDC.Derived.PolishspaceUp
