import BEDC.Derived.NestedIntervalCompactnessUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.NestedIntervalCompactnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NestedIntervalCompactnessCarrier_namecert_obligations
    (I L D W R E H C P N : BHist) :
    nestedIntervalCompactnessFromEventFlow
          (nestedIntervalCompactnessToEventFlow
            (NestedIntervalCompactnessUp.mk I L D W R E H C P N)) =
        some (NestedIntervalCompactnessUp.mk I L D W R E H C P N) ∧
      nestedIntervalCompactnessFields
          (NestedIntervalCompactnessUp.mk I L D W R E H C P N) =
        [I, L, D, W, R, E, H, C, P, N] ∧
      hsame
          (nestedIntervalCompactnessDecodeBHist
            (nestedIntervalCompactnessEncodeBHist I))
          I ∧
      hsame
          (nestedIntervalCompactnessDecodeBHist
            (nestedIntervalCompactnessEncodeBHist D))
          D ∧
      hsame
          (nestedIntervalCompactnessDecodeBHist
            (nestedIntervalCompactnessEncodeBHist E))
          E ∧
      Cont I D (append I D) ∧
      Cont D W (append D W) ∧
      Cont W R (append W R) := by
  -- BEDC touchpoint anchor: BHist BMark hsame Cont
  have hdecode :
      ∀ h : BHist,
        nestedIntervalCompactnessDecodeBHist
            (nestedIntervalCompactnessEncodeBHist h) =
          h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · rw [nestedIntervalCompactnessToEventFlow, nestedIntervalCompactnessFromEventFlow]
    change
      some
          (NestedIntervalCompactnessUp.mk
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist I))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist L))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist D))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist W))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist R))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist E))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist H))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist C))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist P))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist N))) =
        some (NestedIntervalCompactnessUp.mk I L D W R E H C P N)
    rw [hdecode I, hdecode L, hdecode D, hdecode W, hdecode R, hdecode E,
      hdecode H, hdecode C, hdecode P, hdecode N]
  · constructor
    · rfl
    · constructor
      · exact hdecode I
      · constructor
        · exact hdecode D
        · constructor
          · exact hdecode E
          · constructor
            · rfl
            · constructor
              · rfl
              · rfl

theorem NestedIntervalCompactnessCarrier_located_endpoint_scope
    (I L D W R E H C P N : BHist) :
    nestedIntervalCompactnessFromEventFlow
          (nestedIntervalCompactnessToEventFlow
            (NestedIntervalCompactnessUp.mk I L D W R E H C P N)) =
        some (NestedIntervalCompactnessUp.mk I L D W R E H C P N) ∧
      nestedIntervalCompactnessFields
          (NestedIntervalCompactnessUp.mk I L D W R E H C P N) =
        [I, L, D, W, R, E, H, C, P, N] ∧
      hsame
          (nestedIntervalCompactnessDecodeBHist
            (nestedIntervalCompactnessEncodeBHist L))
          L ∧
      Cont I L (append I L) ∧
      Cont L D (append L D) ∧
      Cont D W (append D W) := by
  -- BEDC touchpoint anchor: BHist BMark hsame Cont
  have hdecode :
      ∀ h : BHist,
        nestedIntervalCompactnessDecodeBHist
            (nestedIntervalCompactnessEncodeBHist h) =
          h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · rw [nestedIntervalCompactnessToEventFlow, nestedIntervalCompactnessFromEventFlow]
    change
      some
          (NestedIntervalCompactnessUp.mk
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist I))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist L))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist D))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist W))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist R))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist E))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist H))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist C))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist P))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist N))) =
        some (NestedIntervalCompactnessUp.mk I L D W R E H C P N)
    rw [hdecode I, hdecode L, hdecode D, hdecode W, hdecode R, hdecode E,
      hdecode H, hdecode C, hdecode P, hdecode N]
  · constructor
    · rfl
    · constructor
      · exact hdecode L
      · constructor
        · rfl
        · constructor
          · rfl
          · rfl

theorem NestedIntervalCompactnessCarrier_scope_package
    (I L D W R E H C P N : BHist) :
    nestedIntervalCompactnessFromEventFlow
          (nestedIntervalCompactnessToEventFlow
            (NestedIntervalCompactnessUp.mk I L D W R E H C P N)) =
        some (NestedIntervalCompactnessUp.mk I L D W R E H C P N) ∧
      nestedIntervalCompactnessFields
          (NestedIntervalCompactnessUp.mk I L D W R E H C P N) =
        [I, L, D, W, R, E, H, C, P, N] ∧
      hsame
          (nestedIntervalCompactnessDecodeBHist
            (nestedIntervalCompactnessEncodeBHist I))
          I ∧
      hsame
          (nestedIntervalCompactnessDecodeBHist
            (nestedIntervalCompactnessEncodeBHist L))
          L ∧
      hsame
          (nestedIntervalCompactnessDecodeBHist
            (nestedIntervalCompactnessEncodeBHist D))
          D ∧
      hsame
          (nestedIntervalCompactnessDecodeBHist
            (nestedIntervalCompactnessEncodeBHist W))
          W ∧
      hsame
          (nestedIntervalCompactnessDecodeBHist
            (nestedIntervalCompactnessEncodeBHist R))
          R ∧
      hsame
          (nestedIntervalCompactnessDecodeBHist
            (nestedIntervalCompactnessEncodeBHist E))
          E ∧
      hsame H H ∧
      hsame C C ∧
      hsame P P ∧
      hsame N N ∧
      Cont I L (append I L) ∧
      Cont L D (append L D) ∧
      Cont D W (append D W) ∧
      Cont W R (append W R) ∧
      Cont R E (append R E) := by
  -- BEDC touchpoint anchor: BHist BMark hsame Cont
  have hdecode :
      ∀ h : BHist,
        nestedIntervalCompactnessDecodeBHist
            (nestedIntervalCompactnessEncodeBHist h) =
          h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · rw [nestedIntervalCompactnessToEventFlow, nestedIntervalCompactnessFromEventFlow]
    change
      some
          (NestedIntervalCompactnessUp.mk
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist I))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist L))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist D))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist W))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist R))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist E))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist H))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist C))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist P))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist N))) =
        some (NestedIntervalCompactnessUp.mk I L D W R E H C P N)
    rw [hdecode I, hdecode L, hdecode D, hdecode W, hdecode R, hdecode E,
      hdecode H, hdecode C, hdecode P, hdecode N]
  · constructor
    · rfl
    · constructor
      · exact hdecode I
      · constructor
        · exact hdecode L
        · constructor
          · exact hdecode D
          · constructor
            · exact hdecode W
            · constructor
              · exact hdecode R
              · constructor
                · exact hdecode E
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

theorem NestedIntervalCompactnessCarrier_public_certificate [AskSetup] [PackageSetup]
    {I L D W R E H C P N publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedIntervalCompactnessCarrier I L D W R E H C P N bundle pkg →
      Cont E H publicRead →
        PkgSig bundle publicRead pkg →
          SemanticNameCert
            (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row I ∨ hsame row L ∨ hsame row D ∨ hsame row W ∨
                hsame row R ∨ hsame row E ∨ hsame row publicRead)
            (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier publicRoute publicPkg
  obtain ⟨_iUnary, _lUnary, _dUnary, wUnary, rUnary, hUnary, _windowRoute,
    readbackRoute, _carrierPkg, _sameHC, _sameNN⟩ := carrier
  have eUnary : UnaryHistory E :=
    unary_cont_closed wUnary rUnary readbackRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed eUnary hUnary publicRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact ⟨source.left, publicPkg⟩
  }

end BEDC.Derived.NestedIntervalCompactnessUp
