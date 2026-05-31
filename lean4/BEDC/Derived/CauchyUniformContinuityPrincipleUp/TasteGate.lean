import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyUniformContinuityPrincipleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyUniformContinuityPrincipleUp : Type where
  | mk (S W D U M T E H C P N : BHist) : CauchyUniformContinuityPrincipleUp
  deriving DecidableEq

def cauchyUniformContinuityPrincipleEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyUniformContinuityPrincipleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyUniformContinuityPrincipleEncodeBHist h

def cauchyUniformContinuityPrincipleDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyUniformContinuityPrincipleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyUniformContinuityPrincipleDecodeBHist tail)

private theorem cauchyUniformContinuityPrincipleDecodeEncode :
    forall h : BHist,
      cauchyUniformContinuityPrincipleDecodeBHist
          (cauchyUniformContinuityPrincipleEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyUniformContinuityPrincipleFields :
    CauchyUniformContinuityPrincipleUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyUniformContinuityPrincipleUp.mk S W D U M T E H C P N =>
      [S, W, D, U, M, T, E, H, C, P, N]

def cauchyUniformContinuityPrincipleToEventFlow :
    CauchyUniformContinuityPrincipleUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (cauchyUniformContinuityPrincipleFields x).map
        cauchyUniformContinuityPrincipleEncodeBHist

private def cauchyUniformContinuityPrincipleEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyUniformContinuityPrincipleEventAt index rest

def cauchyUniformContinuityPrincipleFromEventFlow
    (ef : EventFlow) : Option CauchyUniformContinuityPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyUniformContinuityPrincipleUp.mk
      (cauchyUniformContinuityPrincipleDecodeBHist
        (cauchyUniformContinuityPrincipleEventAt 0 ef))
      (cauchyUniformContinuityPrincipleDecodeBHist
        (cauchyUniformContinuityPrincipleEventAt 1 ef))
      (cauchyUniformContinuityPrincipleDecodeBHist
        (cauchyUniformContinuityPrincipleEventAt 2 ef))
      (cauchyUniformContinuityPrincipleDecodeBHist
        (cauchyUniformContinuityPrincipleEventAt 3 ef))
      (cauchyUniformContinuityPrincipleDecodeBHist
        (cauchyUniformContinuityPrincipleEventAt 4 ef))
      (cauchyUniformContinuityPrincipleDecodeBHist
        (cauchyUniformContinuityPrincipleEventAt 5 ef))
      (cauchyUniformContinuityPrincipleDecodeBHist
        (cauchyUniformContinuityPrincipleEventAt 6 ef))
      (cauchyUniformContinuityPrincipleDecodeBHist
        (cauchyUniformContinuityPrincipleEventAt 7 ef))
      (cauchyUniformContinuityPrincipleDecodeBHist
        (cauchyUniformContinuityPrincipleEventAt 8 ef))
      (cauchyUniformContinuityPrincipleDecodeBHist
        (cauchyUniformContinuityPrincipleEventAt 9 ef))
      (cauchyUniformContinuityPrincipleDecodeBHist
        (cauchyUniformContinuityPrincipleEventAt 10 ef)))

private theorem cauchyUniformContinuityPrincipleRoundTrip
    (x : CauchyUniformContinuityPrincipleUp) :
    cauchyUniformContinuityPrincipleFromEventFlow
        (cauchyUniformContinuityPrincipleToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S W D U M T E H C P N =>
      change
        some
          (CauchyUniformContinuityPrincipleUp.mk
            (cauchyUniformContinuityPrincipleDecodeBHist
              (cauchyUniformContinuityPrincipleEncodeBHist S))
            (cauchyUniformContinuityPrincipleDecodeBHist
              (cauchyUniformContinuityPrincipleEncodeBHist W))
            (cauchyUniformContinuityPrincipleDecodeBHist
              (cauchyUniformContinuityPrincipleEncodeBHist D))
            (cauchyUniformContinuityPrincipleDecodeBHist
              (cauchyUniformContinuityPrincipleEncodeBHist U))
            (cauchyUniformContinuityPrincipleDecodeBHist
              (cauchyUniformContinuityPrincipleEncodeBHist M))
            (cauchyUniformContinuityPrincipleDecodeBHist
              (cauchyUniformContinuityPrincipleEncodeBHist T))
            (cauchyUniformContinuityPrincipleDecodeBHist
              (cauchyUniformContinuityPrincipleEncodeBHist E))
            (cauchyUniformContinuityPrincipleDecodeBHist
              (cauchyUniformContinuityPrincipleEncodeBHist H))
            (cauchyUniformContinuityPrincipleDecodeBHist
              (cauchyUniformContinuityPrincipleEncodeBHist C))
            (cauchyUniformContinuityPrincipleDecodeBHist
              (cauchyUniformContinuityPrincipleEncodeBHist P))
            (cauchyUniformContinuityPrincipleDecodeBHist
              (cauchyUniformContinuityPrincipleEncodeBHist N))) =
          some (CauchyUniformContinuityPrincipleUp.mk S W D U M T E H C P N)
      rw [cauchyUniformContinuityPrincipleDecodeEncode S,
        cauchyUniformContinuityPrincipleDecodeEncode W,
        cauchyUniformContinuityPrincipleDecodeEncode D,
        cauchyUniformContinuityPrincipleDecodeEncode U,
        cauchyUniformContinuityPrincipleDecodeEncode M,
        cauchyUniformContinuityPrincipleDecodeEncode T,
        cauchyUniformContinuityPrincipleDecodeEncode E,
        cauchyUniformContinuityPrincipleDecodeEncode H,
        cauchyUniformContinuityPrincipleDecodeEncode C,
        cauchyUniformContinuityPrincipleDecodeEncode P,
        cauchyUniformContinuityPrincipleDecodeEncode N]

private theorem cauchyUniformContinuityPrincipleToEventFlow_injective
    {x y : CauchyUniformContinuityPrincipleUp} :
    cauchyUniformContinuityPrincipleToEventFlow x =
        cauchyUniformContinuityPrincipleToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyUniformContinuityPrincipleFromEventFlow
          (cauchyUniformContinuityPrincipleToEventFlow x) =
        cauchyUniformContinuityPrincipleFromEventFlow
          (cauchyUniformContinuityPrincipleToEventFlow y) :=
    congrArg cauchyUniformContinuityPrincipleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyUniformContinuityPrincipleRoundTrip x).symm
      (Eq.trans hread (cauchyUniformContinuityPrincipleRoundTrip y)))

instance cauchyUniformContinuityPrincipleBHistCarrier :
    BHistCarrier CauchyUniformContinuityPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyUniformContinuityPrincipleToEventFlow
  fromEventFlow := cauchyUniformContinuityPrincipleFromEventFlow

instance cauchyUniformContinuityPrincipleChapterTasteGate :
    ChapterTasteGate CauchyUniformContinuityPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyUniformContinuityPrincipleFromEventFlow
          (cauchyUniformContinuityPrincipleToEventFlow x) =
        some x
    exact cauchyUniformContinuityPrincipleRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyUniformContinuityPrincipleToEventFlow_injective heq)

theorem CauchyUniformContinuityPrincipleTasteGate_single_carrier_alignment :
    (forall h : BHist,
        cauchyUniformContinuityPrincipleDecodeBHist
            (cauchyUniformContinuityPrincipleEncodeBHist h) =
          h) ∧
      Nonempty (BHistCarrier CauchyUniformContinuityPrincipleUp) ∧
        Nonempty (ChapterTasteGate CauchyUniformContinuityPrincipleUp) ∧
          cauchyUniformContinuityPrincipleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨cauchyUniformContinuityPrincipleDecodeEncode,
      ⟨⟨cauchyUniformContinuityPrincipleBHistCarrier⟩,
        ⟨cauchyUniformContinuityPrincipleChapterTasteGate⟩, rfl⟩⟩

end BEDC.Derived.CauchyUniformContinuityPrincipleUp
