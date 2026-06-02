import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BanachOperatorGraphNormUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BanachOperatorGraphNormUp : Type where
  | mk (X Y T Gamma A M Q L H C P N : BHist) : BanachOperatorGraphNormUp
  deriving DecidableEq

def banachOperatorGraphNormEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: banachOperatorGraphNormEncodeBHist h
  | BHist.e1 h => BMark.b1 :: banachOperatorGraphNormEncodeBHist h

def banachOperatorGraphNormDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (banachOperatorGraphNormDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (banachOperatorGraphNormDecodeBHist tail)

private theorem banachOperatorGraphNorm_decode_encode :
    ∀ h : BHist,
      banachOperatorGraphNormDecodeBHist
          (banachOperatorGraphNormEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def banachOperatorGraphNormFields :
    BanachOperatorGraphNormUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BanachOperatorGraphNormUp.mk X Y T Gamma A M Q L H C P N =>
      [X, Y, T, Gamma, A, M, Q, L, H, C, P, N]

def banachOperatorGraphNormToEventFlow :
    BanachOperatorGraphNormUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map banachOperatorGraphNormEncodeBHist
        (banachOperatorGraphNormFields x)

private def banachOperatorGraphNormRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => banachOperatorGraphNormRawAt index rest

def banachOperatorGraphNormFromEventFlow
    (flow : EventFlow) : Option BanachOperatorGraphNormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BanachOperatorGraphNormUp.mk
      (banachOperatorGraphNormDecodeBHist (banachOperatorGraphNormRawAt 0 flow))
      (banachOperatorGraphNormDecodeBHist (banachOperatorGraphNormRawAt 1 flow))
      (banachOperatorGraphNormDecodeBHist (banachOperatorGraphNormRawAt 2 flow))
      (banachOperatorGraphNormDecodeBHist (banachOperatorGraphNormRawAt 3 flow))
      (banachOperatorGraphNormDecodeBHist (banachOperatorGraphNormRawAt 4 flow))
      (banachOperatorGraphNormDecodeBHist (banachOperatorGraphNormRawAt 5 flow))
      (banachOperatorGraphNormDecodeBHist (banachOperatorGraphNormRawAt 6 flow))
      (banachOperatorGraphNormDecodeBHist (banachOperatorGraphNormRawAt 7 flow))
      (banachOperatorGraphNormDecodeBHist (banachOperatorGraphNormRawAt 8 flow))
      (banachOperatorGraphNormDecodeBHist (banachOperatorGraphNormRawAt 9 flow))
      (banachOperatorGraphNormDecodeBHist (banachOperatorGraphNormRawAt 10 flow))
      (banachOperatorGraphNormDecodeBHist (banachOperatorGraphNormRawAt 11 flow)))

private theorem banachOperatorGraphNorm_round_trip :
    ∀ x : BanachOperatorGraphNormUp,
      banachOperatorGraphNormFromEventFlow
          (banachOperatorGraphNormToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y T Gamma A M Q L H C P N =>
      change
        some
          (BanachOperatorGraphNormUp.mk
            (banachOperatorGraphNormDecodeBHist
              (banachOperatorGraphNormEncodeBHist X))
            (banachOperatorGraphNormDecodeBHist
              (banachOperatorGraphNormEncodeBHist Y))
            (banachOperatorGraphNormDecodeBHist
              (banachOperatorGraphNormEncodeBHist T))
            (banachOperatorGraphNormDecodeBHist
              (banachOperatorGraphNormEncodeBHist Gamma))
            (banachOperatorGraphNormDecodeBHist
              (banachOperatorGraphNormEncodeBHist A))
            (banachOperatorGraphNormDecodeBHist
              (banachOperatorGraphNormEncodeBHist M))
            (banachOperatorGraphNormDecodeBHist
              (banachOperatorGraphNormEncodeBHist Q))
            (banachOperatorGraphNormDecodeBHist
              (banachOperatorGraphNormEncodeBHist L))
            (banachOperatorGraphNormDecodeBHist
              (banachOperatorGraphNormEncodeBHist H))
            (banachOperatorGraphNormDecodeBHist
              (banachOperatorGraphNormEncodeBHist C))
            (banachOperatorGraphNormDecodeBHist
              (banachOperatorGraphNormEncodeBHist P))
            (banachOperatorGraphNormDecodeBHist
              (banachOperatorGraphNormEncodeBHist N))) =
          some (BanachOperatorGraphNormUp.mk X Y T Gamma A M Q L H C P N)
      rw [banachOperatorGraphNorm_decode_encode X,
        banachOperatorGraphNorm_decode_encode Y,
        banachOperatorGraphNorm_decode_encode T,
        banachOperatorGraphNorm_decode_encode Gamma,
        banachOperatorGraphNorm_decode_encode A,
        banachOperatorGraphNorm_decode_encode M,
        banachOperatorGraphNorm_decode_encode Q,
        banachOperatorGraphNorm_decode_encode L,
        banachOperatorGraphNorm_decode_encode H,
        banachOperatorGraphNorm_decode_encode C,
        banachOperatorGraphNorm_decode_encode P,
        banachOperatorGraphNorm_decode_encode N]

private theorem banachOperatorGraphNormToEventFlow_injective
    {x y : BanachOperatorGraphNormUp} :
    banachOperatorGraphNormToEventFlow x =
        banachOperatorGraphNormToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      banachOperatorGraphNormFromEventFlow
          (banachOperatorGraphNormToEventFlow x) =
        banachOperatorGraphNormFromEventFlow
          (banachOperatorGraphNormToEventFlow y) :=
    congrArg banachOperatorGraphNormFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (banachOperatorGraphNorm_round_trip x).symm
      (Eq.trans hread (banachOperatorGraphNorm_round_trip y)))

private theorem banachOperatorGraphNorm_field_faithful :
    ∀ x y : BanachOperatorGraphNormUp,
      banachOperatorGraphNormFields x = banachOperatorGraphNormFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ Y₁ T₁ Gamma₁ A₁ M₁ Q₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ Y₂ T₂ Gamma₂ A₂ M₂ Q₂ L₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hX tail0
          injection tail0 with hY tail1
          injection tail1 with hT tail2
          injection tail2 with hGamma tail3
          injection tail3 with hA tail4
          injection tail4 with hM tail5
          injection tail5 with hQ tail6
          injection tail6 with hL tail7
          injection tail7 with hH tail8
          injection tail8 with hC tail9
          injection tail9 with hP tail10
          injection tail10 with hN _
          subst hX
          subst hY
          subst hT
          subst hGamma
          subst hA
          subst hM
          subst hQ
          subst hL
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance banachOperatorGraphNormBHistCarrier :
    BHistCarrier BanachOperatorGraphNormUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := banachOperatorGraphNormToEventFlow
  fromEventFlow := banachOperatorGraphNormFromEventFlow

instance banachOperatorGraphNormChapterTasteGate :
    ChapterTasteGate BanachOperatorGraphNormUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      banachOperatorGraphNormFromEventFlow
          (banachOperatorGraphNormToEventFlow x) =
        some x
    exact banachOperatorGraphNorm_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (banachOperatorGraphNormToEventFlow_injective heq)

instance banachOperatorGraphNormFieldFaithful :
    FieldFaithful BanachOperatorGraphNormUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := banachOperatorGraphNormFields
  field_faithful := banachOperatorGraphNorm_field_faithful

instance banachOperatorGraphNormNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BanachOperatorGraphNormUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BanachOperatorGraphNormUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      BanachOperatorGraphNormUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BanachOperatorGraphNormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  banachOperatorGraphNormChapterTasteGate

theorem BanachOperatorGraphNormTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BanachOperatorGraphNormUp) ∧
      Nonempty (FieldFaithful BanachOperatorGraphNormUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial BanachOperatorGraphNormUp) ∧
          (∀ h : BHist,
            banachOperatorGraphNormDecodeBHist
                (banachOperatorGraphNormEncodeBHist h) =
              h) ∧
            (∀ x : BanachOperatorGraphNormUp,
              banachOperatorGraphNormFromEventFlow
                  (banachOperatorGraphNormToEventFlow x) =
                some x) ∧
              banachOperatorGraphNormEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨Nonempty.intro banachOperatorGraphNormChapterTasteGate,
      Nonempty.intro banachOperatorGraphNormFieldFaithful,
      Nonempty.intro banachOperatorGraphNormNontrivial,
      banachOperatorGraphNorm_decode_encode,
      banachOperatorGraphNorm_round_trip,
      rfl⟩

end BEDC.Derived.BanachOperatorGraphNormUp.TasteGate
