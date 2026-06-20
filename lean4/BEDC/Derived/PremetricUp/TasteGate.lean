import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PremetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PremetricUp : Type where
  | mk (X U D Z S M H C Q N : BHist) : PremetricUp
  deriving DecidableEq

def PremetricTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: PremetricTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: PremetricTasteGate_single_carrier_alignment_encodeBHist h

def PremetricTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (PremetricTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (PremetricTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem PremetricTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      PremetricTasteGate_single_carrier_alignment_decodeBHist
        (PremetricTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def PremetricTasteGate_single_carrier_alignment_fields :
    PremetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PremetricUp.mk X U D Z S M H C Q N => [X, U, D, Z, S, M, H, C, Q, N]

def PremetricTasteGate_single_carrier_alignment_toEventFlow :
    PremetricUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (PremetricTasteGate_single_carrier_alignment_fields x).map
      PremetricTasteGate_single_carrier_alignment_encodeBHist

def PremetricTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option PremetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun eventFlow =>
    match eventFlow with
    | X :: U :: D :: Z :: S :: M :: H :: C :: Q :: N :: [] =>
        some
          (PremetricUp.mk
            (PremetricTasteGate_single_carrier_alignment_decodeBHist X)
            (PremetricTasteGate_single_carrier_alignment_decodeBHist U)
            (PremetricTasteGate_single_carrier_alignment_decodeBHist D)
            (PremetricTasteGate_single_carrier_alignment_decodeBHist Z)
            (PremetricTasteGate_single_carrier_alignment_decodeBHist S)
            (PremetricTasteGate_single_carrier_alignment_decodeBHist M)
            (PremetricTasteGate_single_carrier_alignment_decodeBHist H)
            (PremetricTasteGate_single_carrier_alignment_decodeBHist C)
            (PremetricTasteGate_single_carrier_alignment_decodeBHist Q)
            (PremetricTasteGate_single_carrier_alignment_decodeBHist N))
    | _ => none

private theorem PremetricTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PremetricUp,
      PremetricTasteGate_single_carrier_alignment_fromEventFlow
        (PremetricTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X U D Z S M H C Q N =>
      change
        some
          (PremetricUp.mk
            (PremetricTasteGate_single_carrier_alignment_decodeBHist
              (PremetricTasteGate_single_carrier_alignment_encodeBHist X))
            (PremetricTasteGate_single_carrier_alignment_decodeBHist
              (PremetricTasteGate_single_carrier_alignment_encodeBHist U))
            (PremetricTasteGate_single_carrier_alignment_decodeBHist
              (PremetricTasteGate_single_carrier_alignment_encodeBHist D))
            (PremetricTasteGate_single_carrier_alignment_decodeBHist
              (PremetricTasteGate_single_carrier_alignment_encodeBHist Z))
            (PremetricTasteGate_single_carrier_alignment_decodeBHist
              (PremetricTasteGate_single_carrier_alignment_encodeBHist S))
            (PremetricTasteGate_single_carrier_alignment_decodeBHist
              (PremetricTasteGate_single_carrier_alignment_encodeBHist M))
            (PremetricTasteGate_single_carrier_alignment_decodeBHist
              (PremetricTasteGate_single_carrier_alignment_encodeBHist H))
            (PremetricTasteGate_single_carrier_alignment_decodeBHist
              (PremetricTasteGate_single_carrier_alignment_encodeBHist C))
            (PremetricTasteGate_single_carrier_alignment_decodeBHist
              (PremetricTasteGate_single_carrier_alignment_encodeBHist Q))
            (PremetricTasteGate_single_carrier_alignment_decodeBHist
              (PremetricTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (PremetricUp.mk X U D Z S M H C Q N)
      rw [PremetricTasteGate_single_carrier_alignment_decode_encode X]
      rw [PremetricTasteGate_single_carrier_alignment_decode_encode U]
      rw [PremetricTasteGate_single_carrier_alignment_decode_encode D]
      rw [PremetricTasteGate_single_carrier_alignment_decode_encode Z]
      rw [PremetricTasteGate_single_carrier_alignment_decode_encode S]
      rw [PremetricTasteGate_single_carrier_alignment_decode_encode M]
      rw [PremetricTasteGate_single_carrier_alignment_decode_encode H]
      rw [PremetricTasteGate_single_carrier_alignment_decode_encode C]
      rw [PremetricTasteGate_single_carrier_alignment_decode_encode Q]
      rw [PremetricTasteGate_single_carrier_alignment_decode_encode N]

private theorem PremetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PremetricUp} :
    PremetricTasteGate_single_carrier_alignment_toEventFlow x =
        PremetricTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      PremetricTasteGate_single_carrier_alignment_fromEventFlow
          (PremetricTasteGate_single_carrier_alignment_toEventFlow x) =
        PremetricTasteGate_single_carrier_alignment_fromEventFlow
          (PremetricTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg PremetricTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PremetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PremetricTasteGate_single_carrier_alignment_round_trip y)))

instance premetricBHistCarrier : BHistCarrier PremetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := PremetricTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := PremetricTasteGate_single_carrier_alignment_fromEventFlow

instance premetricChapterTasteGate : ChapterTasteGate PremetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      PremetricTasteGate_single_carrier_alignment_fromEventFlow
        (PremetricTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact PremetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PremetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate PremetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  premetricChapterTasteGate

theorem PremetricTasteGate_single_carrier_alignment :
    (∀ X U D Z S M H C Q N : BHist,
      PremetricTasteGate_single_carrier_alignment_fields
          (PremetricUp.mk X U D Z S M H C Q N) =
        [X, U, D, Z, S, M, H, C, Q, N]) ∧
      (∀ h : BHist,
        PremetricTasteGate_single_carrier_alignment_decodeBHist
          (PremetricTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
        PremetricTasteGate_single_carrier_alignment_encodeBHist (BHist.e1 BHist.Empty) =
          [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨by
      intro X U D Z S M H C Q N
      rfl,
      PremetricTasteGate_single_carrier_alignment_decode_encode,
      rfl⟩

end BEDC.Derived.PremetricUp
