import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DedekindRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DedekindRealUp : Type where
  | mk (L C T R S Q E H K P N : BHist) : DedekindRealUp
  deriving DecidableEq

def dedekindRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dedekindRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dedekindRealEncodeBHist h

def dedekindRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dedekindRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dedekindRealDecodeBHist tail)

private theorem DedekindRealTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      dedekindRealDecodeBHist (dedekindRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dedekindRealFields : DedekindRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DedekindRealUp.mk L C T R S Q E H K P N => [L, C, T, R, S, Q, E, H, K, P, N]

def dedekindRealToEventFlow : DedekindRealUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (dedekindRealFields x).map dedekindRealEncodeBHist

private def dedekindRealEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dedekindRealEventAtDefault index rest

def dedekindRealFromEventFlow
    (ef : EventFlow) : Option DedekindRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DedekindRealUp.mk
      (dedekindRealDecodeBHist (dedekindRealEventAtDefault 0 ef))
      (dedekindRealDecodeBHist (dedekindRealEventAtDefault 1 ef))
      (dedekindRealDecodeBHist (dedekindRealEventAtDefault 2 ef))
      (dedekindRealDecodeBHist (dedekindRealEventAtDefault 3 ef))
      (dedekindRealDecodeBHist (dedekindRealEventAtDefault 4 ef))
      (dedekindRealDecodeBHist (dedekindRealEventAtDefault 5 ef))
      (dedekindRealDecodeBHist (dedekindRealEventAtDefault 6 ef))
      (dedekindRealDecodeBHist (dedekindRealEventAtDefault 7 ef))
      (dedekindRealDecodeBHist (dedekindRealEventAtDefault 8 ef))
      (dedekindRealDecodeBHist (dedekindRealEventAtDefault 9 ef))
      (dedekindRealDecodeBHist (dedekindRealEventAtDefault 10 ef)))

private theorem DedekindRealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DedekindRealUp,
      dedekindRealFromEventFlow
          (dedekindRealToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk L C T R S Q E H K P N =>
      change
        some
          (DedekindRealUp.mk
            (dedekindRealDecodeBHist (dedekindRealEncodeBHist L))
            (dedekindRealDecodeBHist (dedekindRealEncodeBHist C))
            (dedekindRealDecodeBHist (dedekindRealEncodeBHist T))
            (dedekindRealDecodeBHist (dedekindRealEncodeBHist R))
            (dedekindRealDecodeBHist (dedekindRealEncodeBHist S))
            (dedekindRealDecodeBHist (dedekindRealEncodeBHist Q))
            (dedekindRealDecodeBHist (dedekindRealEncodeBHist E))
            (dedekindRealDecodeBHist (dedekindRealEncodeBHist H))
            (dedekindRealDecodeBHist (dedekindRealEncodeBHist K))
            (dedekindRealDecodeBHist (dedekindRealEncodeBHist P))
            (dedekindRealDecodeBHist (dedekindRealEncodeBHist N))) =
          some (DedekindRealUp.mk L C T R S Q E H K P N)
      rw [DedekindRealTasteGate_single_carrier_alignment_decode L,
        DedekindRealTasteGate_single_carrier_alignment_decode C,
        DedekindRealTasteGate_single_carrier_alignment_decode T,
        DedekindRealTasteGate_single_carrier_alignment_decode R,
        DedekindRealTasteGate_single_carrier_alignment_decode S,
        DedekindRealTasteGate_single_carrier_alignment_decode Q,
        DedekindRealTasteGate_single_carrier_alignment_decode E,
        DedekindRealTasteGate_single_carrier_alignment_decode H,
        DedekindRealTasteGate_single_carrier_alignment_decode K,
        DedekindRealTasteGate_single_carrier_alignment_decode P,
        DedekindRealTasteGate_single_carrier_alignment_decode N]

private theorem DedekindRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DedekindRealUp} :
    dedekindRealToEventFlow x = dedekindRealToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dedekindRealFromEventFlow (dedekindRealToEventFlow x) =
        dedekindRealFromEventFlow (dedekindRealToEventFlow y) :=
    congrArg dedekindRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DedekindRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DedekindRealTasteGate_single_carrier_alignment_round_trip y)))

instance dedekindRealBHistCarrier : BHistCarrier DedekindRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dedekindRealToEventFlow
  fromEventFlow := dedekindRealFromEventFlow

instance dedekindRealChapterTasteGate : ChapterTasteGate DedekindRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dedekindRealFromEventFlow (dedekindRealToEventFlow x) = some x
    exact DedekindRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (DedekindRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate DedekindRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dedekindRealChapterTasteGate

theorem DedekindRealTasteGate_single_carrier_alignment :
    (∀ h : BHist, dedekindRealDecodeBHist (dedekindRealEncodeBHist h) = h) ∧
      (∀ x : DedekindRealUp,
        dedekindRealFromEventFlow (dedekindRealToEventFlow x) = some x) ∧
        (∀ x y : DedekindRealUp,
          dedekindRealToEventFlow x = dedekindRealToEventFlow y → x = y) ∧
          dedekindRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨DedekindRealTasteGate_single_carrier_alignment_decode,
      DedekindRealTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        DedekindRealTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DedekindRealUp
