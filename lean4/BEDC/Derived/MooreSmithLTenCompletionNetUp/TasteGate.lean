import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MooreSmithLTenCompletionNetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MooreSmithLTenCompletionNetUp : Type where
  | mk (D T F W R A H C P N : BHist) : MooreSmithLTenCompletionNetUp
  deriving DecidableEq

def mooreSmithLTenCompletionNetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: mooreSmithLTenCompletionNetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: mooreSmithLTenCompletionNetEncodeBHist h

def mooreSmithLTenCompletionNetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (mooreSmithLTenCompletionNetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (mooreSmithLTenCompletionNetDecodeBHist tail)

private theorem mooreSmithLTenCompletionNet_decode_encode :
    ∀ h : BHist,
      mooreSmithLTenCompletionNetDecodeBHist
          (mooreSmithLTenCompletionNetEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def mooreSmithLTenCompletionNetFields :
    MooreSmithLTenCompletionNetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MooreSmithLTenCompletionNetUp.mk D T F W R A H C P N =>
      [D, T, F, W, R, A, H, C, P, N]

def mooreSmithLTenCompletionNetToEventFlow :
    MooreSmithLTenCompletionNetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map mooreSmithLTenCompletionNetEncodeBHist
        (mooreSmithLTenCompletionNetFields x)

private def mooreSmithLTenCompletionNetEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => mooreSmithLTenCompletionNetEventAt index rest

def mooreSmithLTenCompletionNetFromEventFlow :
    EventFlow → Option MooreSmithLTenCompletionNetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (MooreSmithLTenCompletionNetUp.mk
        (mooreSmithLTenCompletionNetDecodeBHist
          (mooreSmithLTenCompletionNetEventAt 0 ef))
        (mooreSmithLTenCompletionNetDecodeBHist
          (mooreSmithLTenCompletionNetEventAt 1 ef))
        (mooreSmithLTenCompletionNetDecodeBHist
          (mooreSmithLTenCompletionNetEventAt 2 ef))
        (mooreSmithLTenCompletionNetDecodeBHist
          (mooreSmithLTenCompletionNetEventAt 3 ef))
        (mooreSmithLTenCompletionNetDecodeBHist
          (mooreSmithLTenCompletionNetEventAt 4 ef))
        (mooreSmithLTenCompletionNetDecodeBHist
          (mooreSmithLTenCompletionNetEventAt 5 ef))
        (mooreSmithLTenCompletionNetDecodeBHist
          (mooreSmithLTenCompletionNetEventAt 6 ef))
        (mooreSmithLTenCompletionNetDecodeBHist
          (mooreSmithLTenCompletionNetEventAt 7 ef))
        (mooreSmithLTenCompletionNetDecodeBHist
          (mooreSmithLTenCompletionNetEventAt 8 ef))
        (mooreSmithLTenCompletionNetDecodeBHist
          (mooreSmithLTenCompletionNetEventAt 9 ef)))

private theorem mooreSmithLTenCompletionNet_round_trip :
    ∀ x : MooreSmithLTenCompletionNetUp,
      mooreSmithLTenCompletionNetFromEventFlow
          (mooreSmithLTenCompletionNetToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D T F W R A H C P N =>
      change
        some
          (MooreSmithLTenCompletionNetUp.mk
            (mooreSmithLTenCompletionNetDecodeBHist
              (mooreSmithLTenCompletionNetEncodeBHist D))
            (mooreSmithLTenCompletionNetDecodeBHist
              (mooreSmithLTenCompletionNetEncodeBHist T))
            (mooreSmithLTenCompletionNetDecodeBHist
              (mooreSmithLTenCompletionNetEncodeBHist F))
            (mooreSmithLTenCompletionNetDecodeBHist
              (mooreSmithLTenCompletionNetEncodeBHist W))
            (mooreSmithLTenCompletionNetDecodeBHist
              (mooreSmithLTenCompletionNetEncodeBHist R))
            (mooreSmithLTenCompletionNetDecodeBHist
              (mooreSmithLTenCompletionNetEncodeBHist A))
            (mooreSmithLTenCompletionNetDecodeBHist
              (mooreSmithLTenCompletionNetEncodeBHist H))
            (mooreSmithLTenCompletionNetDecodeBHist
              (mooreSmithLTenCompletionNetEncodeBHist C))
            (mooreSmithLTenCompletionNetDecodeBHist
              (mooreSmithLTenCompletionNetEncodeBHist P))
            (mooreSmithLTenCompletionNetDecodeBHist
              (mooreSmithLTenCompletionNetEncodeBHist N))) =
          some (MooreSmithLTenCompletionNetUp.mk D T F W R A H C P N)
      rw [mooreSmithLTenCompletionNet_decode_encode D]
      rw [mooreSmithLTenCompletionNet_decode_encode T]
      rw [mooreSmithLTenCompletionNet_decode_encode F]
      rw [mooreSmithLTenCompletionNet_decode_encode W]
      rw [mooreSmithLTenCompletionNet_decode_encode R]
      rw [mooreSmithLTenCompletionNet_decode_encode A]
      rw [mooreSmithLTenCompletionNet_decode_encode H]
      rw [mooreSmithLTenCompletionNet_decode_encode C]
      rw [mooreSmithLTenCompletionNet_decode_encode P]
      rw [mooreSmithLTenCompletionNet_decode_encode N]

private theorem mooreSmithLTenCompletionNetToEventFlow_injective
    {x y : MooreSmithLTenCompletionNetUp} :
    mooreSmithLTenCompletionNetToEventFlow x =
        mooreSmithLTenCompletionNetToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      mooreSmithLTenCompletionNetFromEventFlow
          (mooreSmithLTenCompletionNetToEventFlow x) =
        mooreSmithLTenCompletionNetFromEventFlow
          (mooreSmithLTenCompletionNetToEventFlow y) :=
    congrArg mooreSmithLTenCompletionNetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (mooreSmithLTenCompletionNet_round_trip x).symm
      (Eq.trans hread (mooreSmithLTenCompletionNet_round_trip y)))

def mooreSmithLTenCompletionNetBHistCarrierData :
    BHistCarrier MooreSmithLTenCompletionNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := mooreSmithLTenCompletionNetToEventFlow
  fromEventFlow := mooreSmithLTenCompletionNetFromEventFlow

instance mooreSmithLTenCompletionNetBHistCarrier :
    BHistCarrier MooreSmithLTenCompletionNetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  mooreSmithLTenCompletionNetBHistCarrierData

def mooreSmithLTenCompletionNetChapterTasteGateData :
    @ChapterTasteGate MooreSmithLTenCompletionNetUp
      mooreSmithLTenCompletionNetBHistCarrierData where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      mooreSmithLTenCompletionNetFromEventFlow
          (mooreSmithLTenCompletionNetToEventFlow x) =
        some x
    exact mooreSmithLTenCompletionNet_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (mooreSmithLTenCompletionNetToEventFlow_injective heq)

instance mooreSmithLTenCompletionNetChapterTasteGate :
    ChapterTasteGate MooreSmithLTenCompletionNetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  mooreSmithLTenCompletionNetChapterTasteGateData

theorem MooreSmithLTenCompletionNetTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      mooreSmithLTenCompletionNetDecodeBHist
          (mooreSmithLTenCompletionNetEncodeBHist h) =
        h) ∧
      (∀ x : MooreSmithLTenCompletionNetUp,
        mooreSmithLTenCompletionNetFromEventFlow
            (mooreSmithLTenCompletionNetToEventFlow x) =
          some x) ∧
        mooreSmithLTenCompletionNetFields
            (MooreSmithLTenCompletionNetUp.mk BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty) =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  · constructor
    · intro x
      cases x with
      | mk D T F W R A H C P N =>
          change
            some
              (MooreSmithLTenCompletionNetUp.mk
                (mooreSmithLTenCompletionNetDecodeBHist
                  (mooreSmithLTenCompletionNetEncodeBHist D))
                (mooreSmithLTenCompletionNetDecodeBHist
                  (mooreSmithLTenCompletionNetEncodeBHist T))
                (mooreSmithLTenCompletionNetDecodeBHist
                  (mooreSmithLTenCompletionNetEncodeBHist F))
                (mooreSmithLTenCompletionNetDecodeBHist
                  (mooreSmithLTenCompletionNetEncodeBHist W))
                (mooreSmithLTenCompletionNetDecodeBHist
                  (mooreSmithLTenCompletionNetEncodeBHist R))
                (mooreSmithLTenCompletionNetDecodeBHist
                  (mooreSmithLTenCompletionNetEncodeBHist A))
                (mooreSmithLTenCompletionNetDecodeBHist
                  (mooreSmithLTenCompletionNetEncodeBHist H))
                (mooreSmithLTenCompletionNetDecodeBHist
                  (mooreSmithLTenCompletionNetEncodeBHist C))
                (mooreSmithLTenCompletionNetDecodeBHist
                  (mooreSmithLTenCompletionNetEncodeBHist P))
                (mooreSmithLTenCompletionNetDecodeBHist
                  (mooreSmithLTenCompletionNetEncodeBHist N))) =
              some (MooreSmithLTenCompletionNetUp.mk D T F W R A H C P N)
          rw [mooreSmithLTenCompletionNet_decode_encode D]
          rw [mooreSmithLTenCompletionNet_decode_encode T]
          rw [mooreSmithLTenCompletionNet_decode_encode F]
          rw [mooreSmithLTenCompletionNet_decode_encode W]
          rw [mooreSmithLTenCompletionNet_decode_encode R]
          rw [mooreSmithLTenCompletionNet_decode_encode A]
          rw [mooreSmithLTenCompletionNet_decode_encode H]
          rw [mooreSmithLTenCompletionNet_decode_encode C]
          rw [mooreSmithLTenCompletionNet_decode_encode P]
          rw [mooreSmithLTenCompletionNet_decode_encode N]
    · rfl

end BEDC.Derived.MooreSmithLTenCompletionNetUp
