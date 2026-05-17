import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailThresholdNormalizerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
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

end BEDC.Derived.CauchyTailThresholdNormalizerUp
