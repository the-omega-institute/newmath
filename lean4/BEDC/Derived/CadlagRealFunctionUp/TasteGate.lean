import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CadlagRealFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CadlagRealFunctionUp : Type where
  | mk (F B S R D J E H C P N : BHist) : CadlagRealFunctionUp
  deriving DecidableEq

def cadlagRealFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cadlagRealFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cadlagRealFunctionEncodeBHist h

def cadlagRealFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cadlagRealFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cadlagRealFunctionDecodeBHist tail)

private theorem CadlagRealFunctionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, cadlagRealFunctionDecodeBHist (cadlagRealFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cadlagRealFunctionFields : CadlagRealFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CadlagRealFunctionUp.mk F B S R D J E H C P N => [F, B, S, R, D, J, E, H, C, P, N]

def cadlagRealFunctionToEventFlow : CadlagRealFunctionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cadlagRealFunctionFields x).map cadlagRealFunctionEncodeBHist

private def cadlagRealFunctionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cadlagRealFunctionRawAt index rest

def cadlagRealFunctionFromEventFlow (flow : EventFlow) : Option CadlagRealFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CadlagRealFunctionUp.mk
      (cadlagRealFunctionDecodeBHist (cadlagRealFunctionRawAt 0 flow))
      (cadlagRealFunctionDecodeBHist (cadlagRealFunctionRawAt 1 flow))
      (cadlagRealFunctionDecodeBHist (cadlagRealFunctionRawAt 2 flow))
      (cadlagRealFunctionDecodeBHist (cadlagRealFunctionRawAt 3 flow))
      (cadlagRealFunctionDecodeBHist (cadlagRealFunctionRawAt 4 flow))
      (cadlagRealFunctionDecodeBHist (cadlagRealFunctionRawAt 5 flow))
      (cadlagRealFunctionDecodeBHist (cadlagRealFunctionRawAt 6 flow))
      (cadlagRealFunctionDecodeBHist (cadlagRealFunctionRawAt 7 flow))
      (cadlagRealFunctionDecodeBHist (cadlagRealFunctionRawAt 8 flow))
      (cadlagRealFunctionDecodeBHist (cadlagRealFunctionRawAt 9 flow))
      (cadlagRealFunctionDecodeBHist (cadlagRealFunctionRawAt 10 flow)))

private theorem CadlagRealFunctionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CadlagRealFunctionUp,
      cadlagRealFunctionFromEventFlow (cadlagRealFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F B S R D J E H C P N =>
      change
        some
          (CadlagRealFunctionUp.mk
            (cadlagRealFunctionDecodeBHist (cadlagRealFunctionEncodeBHist F))
            (cadlagRealFunctionDecodeBHist (cadlagRealFunctionEncodeBHist B))
            (cadlagRealFunctionDecodeBHist (cadlagRealFunctionEncodeBHist S))
            (cadlagRealFunctionDecodeBHist (cadlagRealFunctionEncodeBHist R))
            (cadlagRealFunctionDecodeBHist (cadlagRealFunctionEncodeBHist D))
            (cadlagRealFunctionDecodeBHist (cadlagRealFunctionEncodeBHist J))
            (cadlagRealFunctionDecodeBHist (cadlagRealFunctionEncodeBHist E))
            (cadlagRealFunctionDecodeBHist (cadlagRealFunctionEncodeBHist H))
            (cadlagRealFunctionDecodeBHist (cadlagRealFunctionEncodeBHist C))
            (cadlagRealFunctionDecodeBHist (cadlagRealFunctionEncodeBHist P))
            (cadlagRealFunctionDecodeBHist (cadlagRealFunctionEncodeBHist N))) =
          some (CadlagRealFunctionUp.mk F B S R D J E H C P N)
      rw [CadlagRealFunctionTasteGate_single_carrier_alignment_decode F,
        CadlagRealFunctionTasteGate_single_carrier_alignment_decode B,
        CadlagRealFunctionTasteGate_single_carrier_alignment_decode S,
        CadlagRealFunctionTasteGate_single_carrier_alignment_decode R,
        CadlagRealFunctionTasteGate_single_carrier_alignment_decode D,
        CadlagRealFunctionTasteGate_single_carrier_alignment_decode J,
        CadlagRealFunctionTasteGate_single_carrier_alignment_decode E,
        CadlagRealFunctionTasteGate_single_carrier_alignment_decode H,
        CadlagRealFunctionTasteGate_single_carrier_alignment_decode C,
        CadlagRealFunctionTasteGate_single_carrier_alignment_decode P,
        CadlagRealFunctionTasteGate_single_carrier_alignment_decode N]

private theorem cadlagRealFunctionToEventFlow_injective {x y : CadlagRealFunctionUp} :
    cadlagRealFunctionToEventFlow x = cadlagRealFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cadlagRealFunctionFromEventFlow (cadlagRealFunctionToEventFlow x) =
        cadlagRealFunctionFromEventFlow (cadlagRealFunctionToEventFlow y) :=
    congrArg cadlagRealFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CadlagRealFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CadlagRealFunctionTasteGate_single_carrier_alignment_round_trip y)))

instance cadlagRealFunctionBHistCarrier : BHistCarrier CadlagRealFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cadlagRealFunctionToEventFlow
  fromEventFlow := cadlagRealFunctionFromEventFlow

instance cadlagRealFunctionChapterTasteGate : ChapterTasteGate CadlagRealFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cadlagRealFunctionFromEventFlow (cadlagRealFunctionToEventFlow x) = some x
    exact CadlagRealFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cadlagRealFunctionToEventFlow_injective heq)

theorem CadlagRealFunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist, cadlagRealFunctionDecodeBHist (cadlagRealFunctionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CadlagRealFunctionUp) ∧
        Nonempty (ChapterTasteGate CadlagRealFunctionUp) ∧
          cadlagRealFunctionEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CadlagRealFunctionTasteGate_single_carrier_alignment_decode,
      ⟨cadlagRealFunctionBHistCarrier⟩,
      ⟨cadlagRealFunctionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CadlagRealFunctionUp
