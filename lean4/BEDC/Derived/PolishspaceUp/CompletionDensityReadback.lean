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

theorem PolishSpaceCountableDenseReadback [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport replay provenance localName
      densityRead completionRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metric ->
      UnaryHistory complete ->
        UnaryHistory separable ->
          UnaryHistory stream ->
            UnaryHistory readback ->
              UnaryHistory ledger ->
                UnaryHistory transport ->
                  Cont complete stream completionRead ->
                    Cont separable stream densityRead ->
                      Cont ledger transport replay ->
                        Cont replay readback finalRead ->
                          PkgSig bundle provenance pkg ->
                            PkgSig bundle localName pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row finalRead /\ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row metric \/ hsame row complete \/
                                      hsame row separable \/ hsame row stream \/
                                        hsame row readback \/ hsame row ledger \/
                                          hsame row finalRead)
                                  (fun row : BHist =>
                                    UnaryHistory row /\ PkgSig bundle provenance pkg /\
                                      PkgSig bundle localName pkg)
                                  hsame /\
                                UnaryHistory densityRead /\ UnaryHistory completionRead /\
                                  UnaryHistory finalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _metricUnary completeUnary separableUnary streamUnary readbackUnary ledgerUnary
    transportUnary completeStreamCompletion separableStreamDensity ledgerTransportReplay
    replayReadbackFinal provenancePkg localNamePkg
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed completeUnary streamUnary completeStreamCompletion
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed separableUnary streamUnary separableStreamDensity
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed ledgerUnary transportUnary ledgerTransportReplay
  have finalUnary : UnaryHistory finalRead :=
    unary_cont_closed replayUnary readbackUnary replayReadbackFinal
  have sourceFinal :
      (fun row : BHist => hsame row finalRead /\ UnaryHistory row) finalRead := by
    exact And.intro (hsame_refl finalRead) finalUnary
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row finalRead /\ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric \/ hsame row complete \/ hsame row separable \/
              hsame row stream \/ hsame row readback \/ hsame row ledger \/
                hsame row finalRead)
          (fun row : BHist =>
            UnaryHistory row /\ PkgSig bundle provenance pkg /\ PkgSig bundle localName pkg)
          hsame := {
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
          And.intro (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact And.intro source.right (And.intro provenancePkg localNamePkg)
  }
  exact And.intro cert (And.intro densityUnary (And.intro completionUnary finalUnary))

end BEDC.Derived.PolishspaceUp
