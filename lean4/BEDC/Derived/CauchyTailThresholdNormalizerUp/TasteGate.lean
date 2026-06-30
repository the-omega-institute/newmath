import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailThresholdNormalizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Cont
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyTailThresholdNormalizerUp : Type where
  | mk (S M Theta W0 W1 D R A E H C P L N : BHist) :
      CauchyTailThresholdNormalizerUp
  deriving DecidableEq

def cauchyTailThresholdNormalizerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTailThresholdNormalizerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTailThresholdNormalizerEncodeBHist h

def cauchyTailThresholdNormalizerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTailThresholdNormalizerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTailThresholdNormalizerDecodeBHist tail)

private theorem cauchyTailThresholdNormalizer_decode_encode_bhist :
    ∀ h : BHist,
      cauchyTailThresholdNormalizerDecodeBHist
        (cauchyTailThresholdNormalizerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem cauchyTailThresholdNormalizer_mk_congr
    {S S' M M' Theta Theta' W0 W0' W1 W1' D D' R R' A A' E E' H H'
      C C' P P' L L' N N' : BHist}
    (hS : S' = S) (hM : M' = M) (hTheta : Theta' = Theta) (hW0 : W0' = W0)
    (hW1 : W1' = W1) (hD : D' = D) (hR : R' = R) (hA : A' = A)
    (hE : E' = E) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hL : L' = L) (hN : N' = N) :
    CauchyTailThresholdNormalizerUp.mk S' M' Theta' W0' W1' D' R' A' E' H' C' P'
        L' N' =
      CauchyTailThresholdNormalizerUp.mk S M Theta W0 W1 D R A E H C P L N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hM
  cases hTheta
  cases hW0
  cases hW1
  cases hD
  cases hR
  cases hA
  cases hE
  cases hH
  cases hC
  cases hP
  cases hL
  cases hN
  rfl

def cauchyTailThresholdNormalizerFields :
    CauchyTailThresholdNormalizerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailThresholdNormalizerUp.mk S M Theta W0 W1 D R A E H C P L N =>
      [S, M, Theta, W0, W1, D, R, A, E, H, C, P, L, N]

def cauchyTailThresholdNormalizerToEventFlow :
    CauchyTailThresholdNormalizerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyTailThresholdNormalizerFields x).map
      cauchyTailThresholdNormalizerEncodeBHist

def cauchyTailThresholdNormalizerFromEventFlow :
    EventFlow → Option CauchyTailThresholdNormalizerUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: M :: Theta :: W0 :: W1 :: D :: R :: A :: E :: H :: C :: P :: L :: N :: [] =>
      some
        (CauchyTailThresholdNormalizerUp.mk
          (cauchyTailThresholdNormalizerDecodeBHist S)
          (cauchyTailThresholdNormalizerDecodeBHist M)
          (cauchyTailThresholdNormalizerDecodeBHist Theta)
          (cauchyTailThresholdNormalizerDecodeBHist W0)
          (cauchyTailThresholdNormalizerDecodeBHist W1)
          (cauchyTailThresholdNormalizerDecodeBHist D)
          (cauchyTailThresholdNormalizerDecodeBHist R)
          (cauchyTailThresholdNormalizerDecodeBHist A)
          (cauchyTailThresholdNormalizerDecodeBHist E)
          (cauchyTailThresholdNormalizerDecodeBHist H)
          (cauchyTailThresholdNormalizerDecodeBHist C)
          (cauchyTailThresholdNormalizerDecodeBHist P)
          (cauchyTailThresholdNormalizerDecodeBHist L)
          (cauchyTailThresholdNormalizerDecodeBHist N))
  | _ => none

private theorem cauchyTailThresholdNormalizer_round_trip :
    ∀ x : CauchyTailThresholdNormalizerUp,
      cauchyTailThresholdNormalizerFromEventFlow
        (cauchyTailThresholdNormalizerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M Theta W0 W1 D R A E H C P L N =>
      exact
        congrArg some
          (cauchyTailThresholdNormalizer_mk_congr
            (cauchyTailThresholdNormalizer_decode_encode_bhist S)
            (cauchyTailThresholdNormalizer_decode_encode_bhist M)
            (cauchyTailThresholdNormalizer_decode_encode_bhist Theta)
            (cauchyTailThresholdNormalizer_decode_encode_bhist W0)
            (cauchyTailThresholdNormalizer_decode_encode_bhist W1)
            (cauchyTailThresholdNormalizer_decode_encode_bhist D)
            (cauchyTailThresholdNormalizer_decode_encode_bhist R)
            (cauchyTailThresholdNormalizer_decode_encode_bhist A)
            (cauchyTailThresholdNormalizer_decode_encode_bhist E)
            (cauchyTailThresholdNormalizer_decode_encode_bhist H)
            (cauchyTailThresholdNormalizer_decode_encode_bhist C)
            (cauchyTailThresholdNormalizer_decode_encode_bhist P)
            (cauchyTailThresholdNormalizer_decode_encode_bhist L)
            (cauchyTailThresholdNormalizer_decode_encode_bhist N))

private theorem cauchyTailThresholdNormalizerToEventFlow_injective
    {x y : CauchyTailThresholdNormalizerUp} :
    cauchyTailThresholdNormalizerToEventFlow x =
      cauchyTailThresholdNormalizerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyTailThresholdNormalizerFromEventFlow
          (cauchyTailThresholdNormalizerToEventFlow x) =
        cauchyTailThresholdNormalizerFromEventFlow
          (cauchyTailThresholdNormalizerToEventFlow y) :=
    congrArg cauchyTailThresholdNormalizerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyTailThresholdNormalizer_round_trip x).symm
      (Eq.trans hread (cauchyTailThresholdNormalizer_round_trip y)))

private theorem cauchyTailThresholdNormalizer_field_faithful :
    ∀ x y : CauchyTailThresholdNormalizerUp,
      cauchyTailThresholdNormalizerFields x =
        cauchyTailThresholdNormalizerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S M Theta W0 W1 D R A E H C P L N =>
      cases y with
      | mk S' M' Theta' W0' W1' D' R' A' E' H' C' P' L' N' =>
          cases hfields
          rfl

instance cauchyTailThresholdNormalizerBHistCarrier :
    BHistCarrier CauchyTailThresholdNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyTailThresholdNormalizerToEventFlow
  fromEventFlow := cauchyTailThresholdNormalizerFromEventFlow

instance cauchyTailThresholdNormalizerChapterTasteGate :
    ChapterTasteGate CauchyTailThresholdNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyTailThresholdNormalizerFromEventFlow
        (cauchyTailThresholdNormalizerToEventFlow x) = some x
    exact cauchyTailThresholdNormalizer_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyTailThresholdNormalizerToEventFlow_injective heq)

instance cauchyTailThresholdNormalizerFieldFaithful :
    FieldFaithful CauchyTailThresholdNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyTailThresholdNormalizerFields
  field_faithful := cauchyTailThresholdNormalizer_field_faithful

instance cauchyTailThresholdNormalizerNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyTailThresholdNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyTailThresholdNormalizerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      CauchyTailThresholdNormalizerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyTailThresholdNormalizerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyTailThresholdNormalizerChapterTasteGate

theorem CauchyTailThresholdNormalizerCarrier_namecert_obligations
    (T : CauchyTailThresholdNormalizerUp) :
    SemanticNameCert
      (fun row : BHist =>
        ∃ S M Theta W0 W1 D R A E H C P L N : BHist,
          T = CauchyTailThresholdNormalizerUp.mk S M Theta W0 W1 D R A E H C P L N ∧
            hsame row H)
      (fun row : BHist =>
        ∃ S M Theta W0 W1 D R A E H C P L N : BHist,
          T = CauchyTailThresholdNormalizerUp.mk S M Theta W0 W1 D R A E H C P L N ∧
            hsame row H)
      (fun row : BHist =>
        ∃ S M Theta W0 W1 D R A E H C P L N : BHist,
          T = CauchyTailThresholdNormalizerUp.mk S M Theta W0 W1 D R A E H C P L N ∧
            hsame row H)
      hsame := by
  -- BEDC touchpoint anchor: BHist SemanticNameCert hsame NameCert
  cases T with
  | mk S M Theta W0 W1 D R A E H C P L N =>
      exact {
        core := {
          carrier_inhabited :=
            Exists.intro H
              ⟨S, M, Theta, W0, W1, D, R, A, E, H, C, P, L, N, rfl, hsame_refl H⟩
          equiv_refl := by
            intro row _source
            exact hsame_refl row
          equiv_symm := by
            intro _row _other same
            exact hsame_symm same
          equiv_trans := by
            intro _row _middle _other sameLeft sameRight
            exact hsame_trans sameLeft sameRight
          carrier_respects_equiv := by
            intro row other same source
            have sameRow : hsame row H := by
              cases source with
              | intro S' source =>
                  cases source with
                  | intro M' source =>
                      cases source with
                      | intro Theta' source =>
                          cases source with
                          | intro W0' source =>
                              cases source with
                              | intro W1' source =>
                                  cases source with
                                  | intro D' source =>
                                      cases source with
                                      | intro R' source =>
                                          cases source with
                                          | intro A' source =>
                                              cases source with
                                              | intro E' source =>
                                                  cases source with
                                                  | intro H' source =>
                                                      cases source with
                                                      | intro C' source =>
                                                          cases source with
                                                          | intro P' source =>
                                                              cases source with
                                                              | intro L' source =>
                                                                  cases source with
                                                                  | intro N' source =>
                                                                      cases source.left
                                                                      exact source.right
            exact
              ⟨S, M, Theta, W0, W1, D, R, A, E, H, C, P, L, N, rfl,
                hsame_trans (hsame_symm same) sameRow⟩
        }
        pattern_sound := by
          intro _row source
          exact source
        ledger_sound := by
          intro _row source
          exact source
      }

theorem CauchyTailThresholdNormalizerCarrier_noninternalization
    (T : CauchyTailThresholdNormalizerUp) :
    (∃ S M Theta W0 W1 D R A E H C P L N : BHist,
      T = CauchyTailThresholdNormalizerUp.mk S M Theta W0 W1 D R A E H C P L N ∧
        cauchyTailThresholdNormalizerFields T =
          [S, M, Theta, W0, W1, D, R, A, E, H, C, P, L, N] ∧ hsame H H) ∧
      cauchyTailThresholdNormalizerEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark hsame
  cases T with
  | mk S M Theta W0 W1 D R A E H C P L N =>
      exact
        ⟨⟨S, M, Theta, W0, W1, D, R, A, E, H, C, P, L, N, rfl, rfl,
          hsame_refl H⟩, rfl⟩

def CauchyTailThresholdNormalizerCarrier [AskSetup] [PackageSetup]
    (S M Theta W0 W1 D R A E H C P L N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory Theta ∧ UnaryHistory W0 ∧
    UnaryHistory W1 ∧ UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory A ∧
      UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
        UnaryHistory L ∧ UnaryHistory N ∧ Cont Theta W0 W1 ∧ PkgSig bundle P pkg ∧
          PkgSig bundle N pkg

theorem CauchyTailThresholdNormalizerWindowCofinality [AskSetup] [PackageSetup]
    {S M Theta W0 W1 D R A E H C P L N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyTailThresholdNormalizerCarrier S M Theta W0 W1 D R A E H C P L N
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist => (hsame row W0 ∨ hsame row W1) ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row S ∨ hsame row M ∨ hsame row Theta ∨ hsame row W0 ∨
            hsame row W1)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont Theta W0 W1 ∧ PkgSig bundle P pkg ∧
            PkgSig bundle N pkg)
        hsame ∧ UnaryHistory W0 ∧ UnaryHistory W1 := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  obtain ⟨_sUnary, _mUnary, _thetaUnary, w0Unary, w1Unary, _dUnary, _rUnary,
    _aUnary, _eUnary, _hUnary, _cUnary, _pUnary, _lUnary, _nUnary,
    thresholdWindow, pkgP, pkgN⟩ := carrier
  have sourceAtW0 : (hsame W0 W0 ∨ hsame W0 W1) ∧ UnaryHistory W0 :=
    ⟨Or.inl (hsame_refl W0), w0Unary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => (hsame row W0 ∨ hsame row W1) ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row S ∨ hsame row M ∨ hsame row Theta ∨ hsame row W0 ∨
            hsame row W1)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont Theta W0 W1 ∧ PkgSig bundle P pkg ∧
            PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro W0 sourceAtW0
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
        have otherUnary : UnaryHistory _ :=
          unary_transport source.right sameRows
        cases source.left with
        | inl sameW0 =>
            exact ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameW0), otherUnary⟩
        | inr sameW1 =>
            exact ⟨Or.inr (hsame_trans (hsame_symm sameRows) sameW1), otherUnary⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameW0 =>
          exact Or.inr (Or.inr (Or.inr (Or.inl sameW0)))
      | inr sameW1 =>
          exact Or.inr (Or.inr (Or.inr (Or.inr sameW1)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, thresholdWindow, pkgP, pkgN⟩
  }
  exact ⟨cert, w0Unary, w1Unary⟩

end BEDC.Derived.CauchyTailThresholdNormalizerUp
