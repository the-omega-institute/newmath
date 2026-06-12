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

theorem PolishSpaceCompleteSeparableNamecertObligations [AskSetup] [PackageSetup]
    {metric complete separable stream readback realSeal transport replay provenance localName
      completeRead denseRead observationRead replayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metric ->
      UnaryHistory complete ->
        UnaryHistory separable ->
          UnaryHistory stream ->
            UnaryHistory readback ->
              UnaryHistory transport ->
                UnaryHistory replay ->
                  Cont metric complete completeRead ->
                    Cont metric separable denseRead ->
                      Cont completeRead denseRead observationRead ->
                        Cont transport replay replayRead ->
                          Cont observationRead replayRead namedRead ->
                            PkgSig bundle provenance pkg ->
                              PkgSig bundle localName pkg ->
                                PkgSig bundle namedRead pkg ->
                                  SemanticNameCert
                                      (fun row : BHist => hsame row namedRead ∧
                                        UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row metric ∨ hsame row complete ∨
                                          hsame row separable ∨ hsame row stream ∨
                                            hsame row readback ∨ hsame row realSeal ∨
                                              hsame row transport ∨ hsame row replay ∨
                                                hsame row provenance ∨ hsame row localName ∨
                                                  hsame row namedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧
                                          Cont metric complete completeRead ∧
                                            Cont metric separable denseRead ∧
                                              Cont completeRead denseRead observationRead ∧
                                                Cont transport replay replayRead ∧
                                                  Cont observationRead replayRead namedRead ∧
                                                    PkgSig bundle namedRead pkg)
                                      hsame ∧ UnaryHistory completeRead ∧
                                    UnaryHistory denseRead ∧ UnaryHistory observationRead ∧
                                      UnaryHistory replayRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro metricUnary completeUnary separableUnary _streamUnary _readbackUnary transportUnary
    replayUnary metricComplete metricSeparable completeDense transportReplay
    observationReplay provenancePkg localNamePkg namedPkg
  have completeUnaryRead : UnaryHistory completeRead :=
    unary_cont_closed metricUnary completeUnary metricComplete
  have denseUnaryRead : UnaryHistory denseRead :=
    unary_cont_closed metricUnary separableUnary metricSeparable
  have observationUnary : UnaryHistory observationRead :=
    unary_cont_closed completeUnaryRead denseUnaryRead completeDense
  have replayUnaryRead : UnaryHistory replayRead :=
    unary_cont_closed transportUnary replayUnary transportReplay
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed observationUnary replayUnaryRead observationReplay
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
              hsame row stream ∨ hsame row readback ∨ hsame row realSeal ∨
                hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row localName ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont metric complete completeRead ∧
              Cont metric separable denseRead ∧ Cont completeRead denseRead observationRead ∧
                Cont transport replay replayRead ∧ Cont observationRead replayRead namedRead ∧
                  PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, metricComplete, metricSeparable, completeDense, transportReplay,
          observationReplay, namedPkg⟩
  }
  exact
    ⟨cert, completeUnaryRead, denseUnaryRead, observationUnary, replayUnaryRead,
      namedUnary⟩

end BEDC.Derived.PolishspaceUp
