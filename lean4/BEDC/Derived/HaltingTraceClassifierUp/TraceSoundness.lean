import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HaltingTraceClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingTraceClassifier_positive_trace_soundness [AskSetup] [PackageSetup]
    {M h F R D H C P N halted positiveRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ->
      UnaryHistory h ->
        UnaryHistory F ->
          UnaryHistory R ->
            UnaryHistory D ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      Cont h F halted ->
                        Cont R F positiveRead ->
                          Cont positiveRead D namedRead ->
                            PkgSig bundle P pkg ->
                              PkgSig bundle N pkg ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row namedRead /\ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row M \/ hsame row h \/ hsame row F \/
                                        hsame row R \/ hsame row D \/ hsame row H \/
                                          hsame row C \/ hsame row P \/ hsame row N \/
                                            hsame row halted \/ hsame row positiveRead \/
                                              hsame row namedRead)
                                    (fun row : BHist =>
                                      UnaryHistory row /\ Cont h F halted /\
                                        Cont R F positiveRead /\
                                          Cont positiveRead D namedRead /\
                                            PkgSig bundle P pkg /\ PkgSig bundle N pkg)
                                    hsame /\
                                  UnaryHistory halted /\ UnaryHistory positiveRead /\
                                    UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro _unaryM unaryh unaryF unaryR unaryD _unaryH _unaryC _unaryP _unaryN
    traceRoute positiveRoute namedRoute pkgP pkgN
  have haltedUnary : UnaryHistory halted :=
    unary_cont_closed unaryh unaryF traceRoute
  have positiveUnary : UnaryHistory positiveRead :=
    unary_cont_closed unaryR unaryF positiveRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed positiveUnary unaryD namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead /\ UnaryHistory row)
          (fun row : BHist =>
            hsame row M \/ hsame row h \/ hsame row F \/ hsame row R \/
              hsame row D \/ hsame row H \/ hsame row C \/ hsame row P \/
                hsame row N \/ hsame row halted \/ hsame row positiveRead \/
                  hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row /\ Cont h F halted /\ Cont R F positiveRead /\
              Cont positiveRead D namedRead /\ PkgSig bundle P pkg /\
                PkgSig bundle N pkg)
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, traceRoute, positiveRoute, namedRoute, pkgP, pkgN⟩
  }
  exact ⟨cert, haltedUnary, positiveUnary, namedUnary⟩

theorem HaltingTraceClassifier_diagonal_refusal [AskSetup] [PackageSetup]
    {M h F R D H C P N halted positiveRead namedRead escaped : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ->
      UnaryHistory h ->
        UnaryHistory F ->
          UnaryHistory R ->
            UnaryHistory D ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      Cont h F halted ->
                        Cont R F positiveRead ->
                          Cont positiveRead D namedRead ->
                            Cont D escaped namedRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                      (fun row : BHist => hsame row D /\ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row M \/ hsame row h \/ hsame row F \/
                                          hsame row R \/ hsame row D \/ hsame row H \/
                                            hsame row C \/ hsame row P \/ hsame row N \/
                                              hsame row namedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row /\ Cont h F halted /\
                                          Cont R F positiveRead /\
                                            Cont positiveRead D namedRead /\
                                              PkgSig bundle P pkg /\ PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory namedRead ∧
                                      hsame namedRead (append positiveRead D) ∧
                                        hsame namedRead (append D escaped) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro _unaryM _unaryh _unaryF _unaryR unaryD _unaryH _unaryC _unaryP _unaryN
    traceRoute positiveRoute namedRoute escapeRoute pkgP pkgN
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed (unary_cont_closed _unaryR _unaryF positiveRoute) unaryD namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row D /\ UnaryHistory row)
          (fun row : BHist =>
            hsame row M \/ hsame row h \/ hsame row F \/ hsame row R \/
              hsame row D \/ hsame row H \/ hsame row C \/ hsame row P \/
                hsame row N \/ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row /\ Cont h F halted /\ Cont R F positiveRead /\
              Cont positiveRead D namedRead /\ PkgSig bundle P pkg /\
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro D ⟨hsame_refl D, unaryD⟩
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
      right
      right
      right
      right
      left
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, traceRoute, positiveRoute, namedRoute, pkgP, pkgN⟩
  }
  exact ⟨cert, namedUnary, namedRoute, escapeRoute⟩

theorem HaltingTraceClassifier_non_escape [AskSetup] [PackageSetup]
    {M h F R D H C P N halted positiveRead namedRead escaped : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ->
      UnaryHistory h ->
        UnaryHistory F ->
          UnaryHistory R ->
            UnaryHistory D ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      Cont h F halted ->
                        Cont R F positiveRead ->
                          Cont positiveRead D namedRead ->
                            Cont D escaped namedRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row M ∨ hsame row h ∨ hsame row F ∨
                                          hsame row R ∨ hsame row D ∨ hsame row H ∨
                                            hsame row C ∨ hsame row P ∨ hsame row N ∨
                                              hsame row namedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont h F halted ∧
                                          Cont R F positiveRead ∧
                                            Cont positiveRead D namedRead ∧
                                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory namedRead ∧
                                      hsame namedRead (append positiveRead D) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro _unaryM _unaryh _unaryF unaryR unaryD _unaryH _unaryC _unaryP _unaryN
    traceRoute positiveRoute namedRoute _escapeRoute pkgP pkgN
  have positiveUnary : UnaryHistory positiveRead :=
    unary_cont_closed unaryR _unaryF positiveRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed positiveUnary unaryD namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row h ∨ hsame row F ∨ hsame row R ∨
              hsame row D ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont h F halted ∧ Cont R F positiveRead ∧
              Cont positiveRead D namedRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, traceRoute, positiveRoute, namedRoute, pkgP, pkgN⟩
  }
  exact ⟨cert, namedUnary, namedRoute⟩

theorem HaltingTraceClassifier_obligation_closure [AskSetup] [PackageSetup]
    {M h F R D H C P N halted positiveRead namedRead escaped : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ->
      UnaryHistory h ->
        UnaryHistory F ->
          UnaryHistory R ->
            UnaryHistory D ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      Cont h F halted ->
                        Cont R F positiveRead ->
                          Cont positiveRead D namedRead ->
                            Cont D escaped namedRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row M ∨ hsame row h ∨ hsame row F ∨
                                          hsame row R ∨ hsame row D ∨ hsame row H ∨
                                            hsame row C ∨ hsame row P ∨ hsame row N ∨
                                              hsame row namedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont h F halted ∧
                                          Cont R F positiveRead ∧
                                            Cont positiveRead D namedRead ∧
                                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory halted ∧ UnaryHistory positiveRead ∧
                                      UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryM unaryh unaryF unaryR unaryD unaryH unaryC unaryP unaryN traceRoute
    positiveRoute namedRoute escapeRoute pkgP pkgN
  have positiveSurface :=
    HaltingTraceClassifier_positive_trace_soundness unaryM unaryh unaryF unaryR unaryD
      unaryH unaryC unaryP unaryN traceRoute positiveRoute namedRoute pkgP pkgN
  have refusalSurface :=
    HaltingTraceClassifier_diagonal_refusal unaryM unaryh unaryF unaryR unaryD unaryH
      unaryC unaryP unaryN traceRoute positiveRoute namedRoute escapeRoute pkgP pkgN
  have nonEscape :=
    HaltingTraceClassifier_non_escape unaryM unaryh unaryF unaryR unaryD unaryH unaryC
      unaryP unaryN traceRoute positiveRoute namedRoute escapeRoute pkgP pkgN
  exact
    ⟨nonEscape.left, positiveSurface.right.left, positiveSurface.right.right.left,
      refusalSurface.right.left⟩

end BEDC.Derived.HaltingTraceClassifierUp
