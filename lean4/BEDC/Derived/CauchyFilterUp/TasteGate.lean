import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyFilterUp : Type where
  | mk (s d m e r t c P N : BHist) : CauchyFilterUp

def CauchyFilterTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: CauchyFilterTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: CauchyFilterTasteGate_single_carrier_alignment_encodeBHist h

def CauchyFilterTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (CauchyFilterTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (CauchyFilterTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CauchyFilterTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CauchyFilterTasteGate_single_carrier_alignment_decodeBHist
        (CauchyFilterTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CauchyFilterTasteGate_single_carrier_alignment_fields :
    CauchyFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyFilterUp.mk s d m e r t c P N => [s, d, m, e, r, t, c, P, N]

def CauchyFilterTasteGate_single_carrier_alignment_toEventFlow :
    CauchyFilterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (CauchyFilterTasteGate_single_carrier_alignment_fields x).map
        CauchyFilterTasteGate_single_carrier_alignment_encodeBHist

private def CauchyFilterTasteGate_single_carrier_alignment_rawAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _n, [] => []
  | Nat.succ n, _event :: rest =>
      CauchyFilterTasteGate_single_carrier_alignment_rawAt n rest

private def CauchyFilterTasteGate_single_carrier_alignment_lengthEq :
    Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _event :: _rest => false
  | Nat.succ _n, [] => false
  | Nat.succ n, _event :: rest =>
      CauchyFilterTasteGate_single_carrier_alignment_lengthEq n rest

def CauchyFilterTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option CauchyFilterUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match CauchyFilterTasteGate_single_carrier_alignment_lengthEq 9 flow with
      | true =>
          some
            (CauchyFilterUp.mk
              (CauchyFilterTasteGate_single_carrier_alignment_decodeBHist
                (CauchyFilterTasteGate_single_carrier_alignment_rawAt 0 flow))
              (CauchyFilterTasteGate_single_carrier_alignment_decodeBHist
                (CauchyFilterTasteGate_single_carrier_alignment_rawAt 1 flow))
              (CauchyFilterTasteGate_single_carrier_alignment_decodeBHist
                (CauchyFilterTasteGate_single_carrier_alignment_rawAt 2 flow))
              (CauchyFilterTasteGate_single_carrier_alignment_decodeBHist
                (CauchyFilterTasteGate_single_carrier_alignment_rawAt 3 flow))
              (CauchyFilterTasteGate_single_carrier_alignment_decodeBHist
                (CauchyFilterTasteGate_single_carrier_alignment_rawAt 4 flow))
              (CauchyFilterTasteGate_single_carrier_alignment_decodeBHist
                (CauchyFilterTasteGate_single_carrier_alignment_rawAt 5 flow))
              (CauchyFilterTasteGate_single_carrier_alignment_decodeBHist
                (CauchyFilterTasteGate_single_carrier_alignment_rawAt 6 flow))
              (CauchyFilterTasteGate_single_carrier_alignment_decodeBHist
                (CauchyFilterTasteGate_single_carrier_alignment_rawAt 7 flow))
              (CauchyFilterTasteGate_single_carrier_alignment_decodeBHist
                (CauchyFilterTasteGate_single_carrier_alignment_rawAt 8 flow)))
      | false => none

private theorem CauchyFilterTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyFilterUp,
      CauchyFilterTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyFilterTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk s d m e r t c P N =>
      change
        some
          (CauchyFilterUp.mk
            (CauchyFilterTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterTasteGate_single_carrier_alignment_encodeBHist s))
            (CauchyFilterTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterTasteGate_single_carrier_alignment_encodeBHist d))
            (CauchyFilterTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterTasteGate_single_carrier_alignment_encodeBHist m))
            (CauchyFilterTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterTasteGate_single_carrier_alignment_encodeBHist e))
            (CauchyFilterTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterTasteGate_single_carrier_alignment_encodeBHist r))
            (CauchyFilterTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterTasteGate_single_carrier_alignment_encodeBHist t))
            (CauchyFilterTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterTasteGate_single_carrier_alignment_encodeBHist c))
            (CauchyFilterTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterTasteGate_single_carrier_alignment_encodeBHist P))
            (CauchyFilterTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (CauchyFilterUp.mk s d m e r t c P N)
      rw [CauchyFilterTasteGate_single_carrier_alignment_decode_encode s,
        CauchyFilterTasteGate_single_carrier_alignment_decode_encode d,
        CauchyFilterTasteGate_single_carrier_alignment_decode_encode m,
        CauchyFilterTasteGate_single_carrier_alignment_decode_encode e,
        CauchyFilterTasteGate_single_carrier_alignment_decode_encode r,
        CauchyFilterTasteGate_single_carrier_alignment_decode_encode t,
        CauchyFilterTasteGate_single_carrier_alignment_decode_encode c,
        CauchyFilterTasteGate_single_carrier_alignment_decode_encode P,
        CauchyFilterTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyFilterTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyFilterUp} :
    CauchyFilterTasteGate_single_carrier_alignment_toEventFlow x =
        CauchyFilterTasteGate_single_carrier_alignment_toEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CauchyFilterTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyFilterTasteGate_single_carrier_alignment_toEventFlow x) =
        CauchyFilterTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyFilterTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CauchyFilterTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyFilterTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyFilterTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyFilterBHistCarrier : BHistCarrier CauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CauchyFilterTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CauchyFilterTasteGate_single_carrier_alignment_fromEventFlow

instance cauchyFilterChapterTasteGate : ChapterTasteGate CauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CauchyFilterTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyFilterTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CauchyFilterTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyFilterTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyFilterTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        CauchyFilterTasteGate_single_carrier_alignment_decodeBHist
            (CauchyFilterTasteGate_single_carrier_alignment_encodeBHist h) =
          h) ∧
      CauchyFilterTasteGate_single_carrier_alignment_fields
          (CauchyFilterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨CauchyFilterTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.CauchyFilterUp
