import BEDC.Derived.RegularCauchyFilterUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyFilterCarrier_namecert_obligations [AskSetup] [PackageSetup]
    (B R T D M E H C P N : BHist) :
    regularCauchyFilterFromEventFlow
          (regularCauchyFilterToEventFlow (RegularCauchyFilterUp.mk B R T D M E H C P N)) =
        some (RegularCauchyFilterUp.mk B R T D M E H C P N) ∧
      Cont B T (append B T) ∧
      Cont M E (append M E) ∧
      hsame H H ∧
      hsame C C ∧
      hsame P P ∧
      hsame N N := by
  -- BEDC touchpoint anchor: BHist BMark
  have hdecode :
      ∀ h : BHist, regularCauchyFilterDecodeBHist (regularCauchyFilterEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · rw [regularCauchyFilterToEventFlow, regularCauchyFilterFromEventFlow,
      hdecode B, hdecode R, hdecode T, hdecode D, hdecode M, hdecode E,
      hdecode H, hdecode C, hdecode P, hdecode N]
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · constructor
            · rfl
            · rfl

theorem RegularCauchyFilterCarrier_real_seal_route [AskSetup] [PackageSetup]
    (B R T D M E H C P N : BHist) :
    regularCauchyFilterFromEventFlow
          (regularCauchyFilterToEventFlow (RegularCauchyFilterUp.mk B R T D M E H C P N)) =
        some (RegularCauchyFilterUp.mk B R T D M E H C P N) ∧
      Cont B T (append B T) ∧
      Cont D M (append D M) ∧
      Cont R E (append R E) ∧
      hsame H H ∧
      hsame C C ∧
      hsame P P ∧
      hsame N N := by
  -- BEDC touchpoint anchor: BHist BMark hsame Cont
  have hdecode :
      ∀ h : BHist, regularCauchyFilterDecodeBHist (regularCauchyFilterEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · rw [regularCauchyFilterToEventFlow, regularCauchyFilterFromEventFlow,
      hdecode B, hdecode R, hdecode T, hdecode D, hdecode M, hdecode E,
      hdecode H, hdecode C, hdecode P, hdecode N]
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · constructor
            · rfl
            · constructor
              · rfl
              · rfl

theorem RegularCauchyFilterCarrier_tail_meet [AskSetup] [PackageSetup]
    (B R T D M E H C P N : BHist) :
    regularCauchyFilterFromEventFlow
          (regularCauchyFilterToEventFlow (RegularCauchyFilterUp.mk B R T D M E H C P N)) =
        some (RegularCauchyFilterUp.mk B R T D M E H C P N) ∧
      Cont T D (append T D) ∧
      Cont D M (append D M) ∧
      Cont M R (append M R) ∧
      hsame H H ∧
      hsame C C ∧
      hsame P P ∧
      hsame N N := by
  -- BEDC touchpoint anchor: BHist BMark hsame Cont
  have hdecode :
      ∀ h : BHist, regularCauchyFilterDecodeBHist (regularCauchyFilterEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · rw [regularCauchyFilterToEventFlow, regularCauchyFilterFromEventFlow,
      hdecode B, hdecode R, hdecode T, hdecode D, hdecode M, hdecode E,
      hdecode H, hdecode C, hdecode P, hdecode N]
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · constructor
            · rfl
            · constructor
              · rfl
              · rfl

theorem RegularCauchyFilterCarrier_basis_factorization [AskSetup] [PackageSetup]
    (B R T D M E H C P N : BHist) :
    regularCauchyFilterFromEventFlow
          (regularCauchyFilterToEventFlow (RegularCauchyFilterUp.mk B R T D M E H C P N)) =
        some (RegularCauchyFilterUp.mk B R T D M E H C P N) ∧
      Cont B T (append B T) ∧
      Cont T D (append T D) ∧
      Cont D M (append D M) ∧
      Cont M B (append M B) ∧
      hsame R R ∧
      hsame E E ∧
      hsame H H ∧
      hsame C C ∧
      hsame P P ∧
      hsame N N := by
  -- BEDC touchpoint anchor: BHist BMark hsame Cont
  have hdecode :
      ∀ h : BHist, regularCauchyFilterDecodeBHist (regularCauchyFilterEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · rw [regularCauchyFilterToEventFlow, regularCauchyFilterFromEventFlow,
      hdecode B, hdecode R, hdecode T, hdecode D, hdecode M, hdecode E,
      hdecode H, hdecode C, hdecode P, hdecode N]
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · constructor
            · rfl
            · constructor
              · rfl
              · constructor
                · rfl
                · constructor
                  · rfl
                  · constructor
                    · rfl
                    · rfl

theorem RegularCauchyFilterCarrier_obligation_scope_package [AskSetup] [PackageSetup]
    (B R T D M E H C P N : BHist) :
    regularCauchyFilterFromEventFlow
          (regularCauchyFilterToEventFlow (RegularCauchyFilterUp.mk B R T D M E H C P N)) =
        some (RegularCauchyFilterUp.mk B R T D M E H C P N) ∧
      Cont B T (append B T) ∧
      Cont T D (append T D) ∧
      Cont D M (append D M) ∧
      Cont M E (append M E) ∧
      hsame H H ∧
      hsame C C ∧
      hsame P P ∧
      hsame N N := by
  -- BEDC touchpoint anchor: BHist BMark hsame Cont
  have hdecode :
      ∀ h : BHist, regularCauchyFilterDecodeBHist (regularCauchyFilterEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · rw [regularCauchyFilterToEventFlow, regularCauchyFilterFromEventFlow,
      hdecode B, hdecode R, hdecode T, hdecode D, hdecode M, hdecode E,
      hdecode H, hdecode C, hdecode P, hdecode N]
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · constructor
            · rfl
            · constructor
              · rfl
              · constructor
                · rfl
                · rfl

theorem RegularCauchyFilterCarrier_branch_exhaustion [AskSetup] [PackageSetup]
    (B R T D M E H C P N : BHist) :
    regularCauchyFilterFromEventFlow
          (regularCauchyFilterToEventFlow (RegularCauchyFilterUp.mk B R T D M E H C P N)) =
        some (RegularCauchyFilterUp.mk B R T D M E H C P N) ∧
      Cont B T (append B T) ∧
      Cont T D (append T D) ∧
      Cont D M (append D M) ∧
      Cont M R (append M R) ∧
      Cont R E (append R E) ∧
      hsame H H ∧
      hsame C C ∧
      hsame P P ∧
      hsame N N := by
  -- BEDC touchpoint anchor: BHist BMark hsame Cont
  have hdecode :
      ∀ h : BHist, regularCauchyFilterDecodeBHist (regularCauchyFilterEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · rw [regularCauchyFilterToEventFlow, regularCauchyFilterFromEventFlow,
      hdecode B, hdecode R, hdecode T, hdecode D, hdecode M, hdecode E,
      hdecode H, hdecode C, hdecode P, hdecode N]
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · constructor
            · rfl
            · constructor
              · rfl
              · constructor
                · rfl
                · constructor
                  · rfl
                  · rfl

theorem RegularCauchyFilterCarrier_tail_window_exactness [AskSetup] [PackageSetup]
    (B R T D M E H C P N : BHist) :
    regularCauchyFilterFromEventFlow
          (regularCauchyFilterToEventFlow (RegularCauchyFilterUp.mk B R T D M E H C P N)) =
        some (RegularCauchyFilterUp.mk B R T D M E H C P N) ∧
      Cont T D (append T D) ∧
      Cont D M (append D M) ∧
      Cont M E (append M E) ∧
      Cont E H (append E H) ∧
      hsame C C ∧
      hsame P P ∧
      hsame N N := by
  -- BEDC touchpoint anchor: BHist BMark hsame Cont
  have hdecode :
      ∀ h : BHist, regularCauchyFilterDecodeBHist (regularCauchyFilterEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · rw [regularCauchyFilterToEventFlow, regularCauchyFilterFromEventFlow,
      hdecode B, hdecode R, hdecode T, hdecode D, hdecode M, hdecode E,
      hdecode H, hdecode C, hdecode P, hdecode N]
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · constructor
            · rfl
            · constructor
              · rfl
              · rfl

theorem RegularCauchyFilterCarrier_ledger [AskSetup] [PackageSetup]
    {B R T D M E H C P N ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B -> UnaryHistory T -> UnaryHistory D -> UnaryHistory M ->
      UnaryHistory R -> UnaryHistory E -> Cont B T (append B T) ->
        Cont T D (append T D) -> Cont D M (append D M) ->
          Cont M R (append M R) -> Cont R E ledgerRead ->
            PkgSig bundle ledgerRead pkg ->
              UnaryHistory ledgerRead ∧ Cont B T (append B T) ∧
                Cont T D (append T D) ∧ Cont D M (append D M) ∧
                  Cont M R (append M R) ∧ Cont R E ledgerRead ∧
                    PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro _bUnary _tUnary _dUnary _mUnary rUnary eUnary baseTail tailDyadic
    dyadicMeet meetRead readSeal ledgerPkg
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed rUnary eUnary readSeal
  exact
    ⟨ledgerUnary, baseTail, tailDyadic, dyadicMeet, meetRead, readSeal, ledgerPkg⟩

theorem RegularCauchyFilterCarrier_basis_witness_admission [AskSetup] [PackageSetup]
    {B R T D M E H C P N basisRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B ->
      UnaryHistory T ->
        UnaryHistory D ->
          UnaryHistory M ->
            Cont B T (append B T) ->
              Cont T D (append T D) ->
                Cont (append T D) M basisRead ->
                  PkgSig bundle basisRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row basisRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row B ∨ hsame row T ∨ hsame row D ∨ hsame row M ∨
                            Cont (append T D) M basisRead)
                        (fun row : BHist => PkgSig bundle basisRead pkg ∧ hsame row basisRead)
                        hsame ∧
                      UnaryHistory basisRead ∧ Cont B T (append B T) ∧
                        Cont T D (append T D) ∧ Cont (append T D) M basisRead ∧
                          PkgSig bundle basisRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro _bUnary tUnary dUnary mUnary baseTail tailDyadic dyadicMeet basisPkg
  have tailDyadicUnary : UnaryHistory (append T D) :=
    unary_cont_closed tUnary dUnary tailDyadic
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed tailDyadicUnary mUnary dyadicMeet
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row basisRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row T ∨ hsame row D ∨ hsame row M ∨
              Cont (append T D) M basisRead)
          (fun row : BHist => PkgSig bundle basisRead pkg ∧ hsame row basisRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro basisRead ⟨hsame_refl basisRead, basisUnary⟩
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
        intro row other sameRows source
        have otherSame : hsame other basisRead :=
          hsame_trans (hsame_symm sameRows) source.left
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        exact ⟨otherSame, otherUnary⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr dyadicMeet)))
    ledger_sound := by
      intro _row source
      exact ⟨basisPkg, source.left⟩
  }
  exact ⟨cert, basisUnary, baseTail, tailDyadic, dyadicMeet, basisPkg⟩

theorem RegularCauchyFilterCarrier_tail_basis_exhaustion [AskSetup] [PackageSetup]
    {B T D M basisRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B ->
      UnaryHistory T ->
        UnaryHistory D ->
          UnaryHistory M ->
            Cont B T (append B T) ->
              Cont T D (append T D) ->
                Cont (append T D) M basisRead ->
                  PkgSig bundle basisRead pkg ->
                    UnaryHistory (append B T) ∧ UnaryHistory (append T D) ∧
                      UnaryHistory basisRead ∧ Cont B T (append B T) ∧
                        Cont T D (append T D) ∧ Cont (append T D) M basisRead ∧
                          PkgSig bundle basisRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro bUnary tUnary dUnary mUnary baseTail tailDyadic dyadicMeet basisPkg
  have baseTailUnary : UnaryHistory (append B T) :=
    unary_cont_closed bUnary tUnary baseTail
  have tailDyadicUnary : UnaryHistory (append T D) :=
    unary_cont_closed tUnary dUnary tailDyadic
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed tailDyadicUnary mUnary dyadicMeet
  exact
    ⟨baseTailUnary, tailDyadicUnary, basisUnary, baseTail, tailDyadic, dyadicMeet,
      basisPkg⟩

theorem RegularCauchyFilterCarrier_directed_tail_closure [AskSetup] [PackageSetup]
    (B R T D M E H C P N : BHist) :
    regularCauchyFilterFromEventFlow
          (regularCauchyFilterToEventFlow (RegularCauchyFilterUp.mk B R T D M E H C P N)) =
        some (RegularCauchyFilterUp.mk B R T D M E H C P N) ∧
      Cont T D (append T D) ∧
      Cont D M (append D M) ∧
      Cont M R (append M R) ∧
      Cont R E (append R E) ∧
      hsame H H ∧
      hsame C C ∧
      hsame P P ∧
      hsame N N := by
  -- BEDC touchpoint anchor: BHist BMark hsame Cont
  have hdecode :
      ∀ h : BHist, regularCauchyFilterDecodeBHist (regularCauchyFilterEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · rw [regularCauchyFilterToEventFlow, regularCauchyFilterFromEventFlow,
      hdecode B, hdecode R, hdecode T, hdecode D, hdecode M, hdecode E,
      hdecode H, hdecode C, hdecode P, hdecode N]
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · constructor
            · rfl
            · constructor
              · rfl
              · constructor
                · rfl
                · rfl

theorem RegularCauchyFilterCarrier_regseqrat_window_exposure [AskSetup] [PackageSetup]
    {B R T D M E H C P N basisRead regReadback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T ->
      UnaryHistory D ->
        UnaryHistory M ->
          UnaryHistory R ->
            Cont T D (append T D) ->
              Cont (append T D) M basisRead ->
                Cont basisRead R regReadback ->
                  PkgSig bundle regReadback pkg ->
                    regularCauchyFilterFromEventFlow
                        (regularCauchyFilterToEventFlow
                          (RegularCauchyFilterUp.mk B R T D M E H C P N)) =
                      some (RegularCauchyFilterUp.mk B R T D M E H C P N) ∧
                      SemanticNameCert
                          (fun row : BHist => hsame row regReadback ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row B ∨ hsame row T ∨ hsame row D ∨ hsame row M ∨
                              hsame row R ∨ Cont basisRead R regReadback)
                          (fun row : BHist => PkgSig bundle regReadback pkg ∧
                            hsame row regReadback)
                          hsame ∧
                        UnaryHistory regReadback ∧ Cont basisRead R regReadback ∧
                          PkgSig bundle regReadback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro tUnary dUnary mUnary rUnary tailDyadic dyadicMeet readbackRoute readbackPkg
  have hdecode :
      ∀ h : BHist, regularCauchyFilterDecodeBHist (regularCauchyFilterEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed (unary_cont_closed tUnary dUnary tailDyadic) mUnary dyadicMeet
  have readbackUnary : UnaryHistory regReadback :=
    unary_cont_closed basisUnary rUnary readbackRoute
  have roundTrip :
      regularCauchyFilterFromEventFlow
          (regularCauchyFilterToEventFlow
            (RegularCauchyFilterUp.mk B R T D M E H C P N)) =
        some (RegularCauchyFilterUp.mk B R T D M E H C P N) := by
    rw [regularCauchyFilterToEventFlow, regularCauchyFilterFromEventFlow,
      hdecode B, hdecode R, hdecode T, hdecode D, hdecode M, hdecode E,
      hdecode H, hdecode C, hdecode P, hdecode N]
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row regReadback ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row T ∨ hsame row D ∨ hsame row M ∨
              hsame row R ∨ Cont basisRead R regReadback)
          (fun row : BHist => PkgSig bundle regReadback pkg ∧ hsame row regReadback)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro regReadback ⟨hsame_refl regReadback, readbackUnary⟩
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
        intro row other sameRows source
        have otherSame : hsame other regReadback :=
          hsame_trans (hsame_symm sameRows) source.left
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        exact ⟨otherSame, otherUnary⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr readbackRoute))))
    ledger_sound := by
      intro _row source
      exact ⟨readbackPkg, source.left⟩
  }
  exact ⟨roundTrip, cert, readbackUnary, readbackRoute, readbackPkg⟩

end BEDC.Derived.RegularCauchyFilterUp
