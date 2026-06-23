import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyMatrixUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyMatrixUp : Type where
  | mk (R C W D Q E H K P N : BHist) : CauchyMatrixUp

def cauchyMatrixEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyMatrixEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyMatrixEncodeBHist h

def cauchyMatrixDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyMatrixDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyMatrixDecodeBHist tail)

private theorem cauchyMatrixDecodeEncode :
    ∀ h : BHist, cauchyMatrixDecodeBHist (cauchyMatrixEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyMatrixFields : CauchyMatrixUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyMatrixUp.mk R C W D Q E H K P N => [R, C, W, D, Q, E, H, K, P, N]

def cauchyMatrixToEventFlow : CauchyMatrixUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyMatrixFields x).map cauchyMatrixEncodeBHist

private def cauchyMatrixEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyMatrixEventAt index rest

def cauchyMatrixFromEventFlow (ef : EventFlow) : Option CauchyMatrixUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyMatrixUp.mk
      (cauchyMatrixDecodeBHist (cauchyMatrixEventAt 0 ef))
      (cauchyMatrixDecodeBHist (cauchyMatrixEventAt 1 ef))
      (cauchyMatrixDecodeBHist (cauchyMatrixEventAt 2 ef))
      (cauchyMatrixDecodeBHist (cauchyMatrixEventAt 3 ef))
      (cauchyMatrixDecodeBHist (cauchyMatrixEventAt 4 ef))
      (cauchyMatrixDecodeBHist (cauchyMatrixEventAt 5 ef))
      (cauchyMatrixDecodeBHist (cauchyMatrixEventAt 6 ef))
      (cauchyMatrixDecodeBHist (cauchyMatrixEventAt 7 ef))
      (cauchyMatrixDecodeBHist (cauchyMatrixEventAt 8 ef))
      (cauchyMatrixDecodeBHist (cauchyMatrixEventAt 9 ef)))

private theorem cauchyMatrixRoundTrip (x : CauchyMatrixUp) :
    cauchyMatrixFromEventFlow (cauchyMatrixToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R C W D Q E H K P N =>
      change
        some
          (CauchyMatrixUp.mk
            (cauchyMatrixDecodeBHist (cauchyMatrixEncodeBHist R))
            (cauchyMatrixDecodeBHist (cauchyMatrixEncodeBHist C))
            (cauchyMatrixDecodeBHist (cauchyMatrixEncodeBHist W))
            (cauchyMatrixDecodeBHist (cauchyMatrixEncodeBHist D))
            (cauchyMatrixDecodeBHist (cauchyMatrixEncodeBHist Q))
            (cauchyMatrixDecodeBHist (cauchyMatrixEncodeBHist E))
            (cauchyMatrixDecodeBHist (cauchyMatrixEncodeBHist H))
            (cauchyMatrixDecodeBHist (cauchyMatrixEncodeBHist K))
            (cauchyMatrixDecodeBHist (cauchyMatrixEncodeBHist P))
            (cauchyMatrixDecodeBHist (cauchyMatrixEncodeBHist N))) =
          some (CauchyMatrixUp.mk R C W D Q E H K P N)
      rw [cauchyMatrixDecodeEncode R, cauchyMatrixDecodeEncode C,
        cauchyMatrixDecodeEncode W, cauchyMatrixDecodeEncode D,
        cauchyMatrixDecodeEncode Q, cauchyMatrixDecodeEncode E,
        cauchyMatrixDecodeEncode H, cauchyMatrixDecodeEncode K,
        cauchyMatrixDecodeEncode P, cauchyMatrixDecodeEncode N]

private theorem cauchyMatrixToEventFlow_injective {x y : CauchyMatrixUp} :
    cauchyMatrixToEventFlow x = cauchyMatrixToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyMatrixFromEventFlow (cauchyMatrixToEventFlow x) =
        cauchyMatrixFromEventFlow (cauchyMatrixToEventFlow y) :=
    congrArg cauchyMatrixFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyMatrixRoundTrip x).symm
      (Eq.trans hread (cauchyMatrixRoundTrip y)))

instance cauchyMatrixBHistCarrier : BHistCarrier CauchyMatrixUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyMatrixToEventFlow
  fromEventFlow := cauchyMatrixFromEventFlow

instance cauchyMatrixChapterTasteGate : ChapterTasteGate CauchyMatrixUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyMatrixFromEventFlow (cauchyMatrixToEventFlow x) = some x
    exact cauchyMatrixRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyMatrixToEventFlow_injective heq)

theorem CauchyMatrixTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyMatrixDecodeBHist (cauchyMatrixEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyMatrixUp) ∧
        Nonempty (ChapterTasteGate CauchyMatrixUp) ∧
          cauchyMatrixEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨cauchyMatrixDecodeEncode, ⟨cauchyMatrixBHistCarrier⟩,
      ⟨cauchyMatrixChapterTasteGate⟩, rfl⟩

end BEDC.Derived.CauchyMatrixUp
