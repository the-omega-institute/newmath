import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FrechetRieszUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FrechetRieszUp : Type where
  | mk (H I L V E K P R T C Q N : BHist) : FrechetRieszUp
  deriving DecidableEq

def frechetRieszEncodeBHist : BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: frechetRieszEncodeBHist h
  | BHist.e1 h => BMark.b1 :: frechetRieszEncodeBHist h

def frechetRieszDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (frechetRieszDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (frechetRieszDecodeBHist tail)

private theorem FrechetRieszTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, frechetRieszDecodeBHist (frechetRieszEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def frechetRieszFields : FrechetRieszUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FrechetRieszUp.mk H I L V E K P R T C Q N => [H, I, L, V, E, K, P, R, T, C, Q, N]

def frechetRieszToEventFlow : FrechetRieszUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (frechetRieszFields x).map frechetRieszEncodeBHist

private def frechetRieszEventAtDefault : Nat → EventFlow → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => frechetRieszEventAtDefault index rest

def frechetRieszFromEventFlow (ef : EventFlow) : Option FrechetRieszUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FrechetRieszUp.mk
      (frechetRieszDecodeBHist (frechetRieszEventAtDefault 0 ef))
      (frechetRieszDecodeBHist (frechetRieszEventAtDefault 1 ef))
      (frechetRieszDecodeBHist (frechetRieszEventAtDefault 2 ef))
      (frechetRieszDecodeBHist (frechetRieszEventAtDefault 3 ef))
      (frechetRieszDecodeBHist (frechetRieszEventAtDefault 4 ef))
      (frechetRieszDecodeBHist (frechetRieszEventAtDefault 5 ef))
      (frechetRieszDecodeBHist (frechetRieszEventAtDefault 6 ef))
      (frechetRieszDecodeBHist (frechetRieszEventAtDefault 7 ef))
      (frechetRieszDecodeBHist (frechetRieszEventAtDefault 8 ef))
      (frechetRieszDecodeBHist (frechetRieszEventAtDefault 9 ef))
      (frechetRieszDecodeBHist (frechetRieszEventAtDefault 10 ef))
      (frechetRieszDecodeBHist (frechetRieszEventAtDefault 11 ef)))

private theorem FrechetRieszTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FrechetRieszUp, frechetRieszFromEventFlow (frechetRieszToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk H I L V E K P R T C Q N =>
      change
        some
          (FrechetRieszUp.mk
            (frechetRieszDecodeBHist (frechetRieszEncodeBHist H))
            (frechetRieszDecodeBHist (frechetRieszEncodeBHist I))
            (frechetRieszDecodeBHist (frechetRieszEncodeBHist L))
            (frechetRieszDecodeBHist (frechetRieszEncodeBHist V))
            (frechetRieszDecodeBHist (frechetRieszEncodeBHist E))
            (frechetRieszDecodeBHist (frechetRieszEncodeBHist K))
            (frechetRieszDecodeBHist (frechetRieszEncodeBHist P))
            (frechetRieszDecodeBHist (frechetRieszEncodeBHist R))
            (frechetRieszDecodeBHist (frechetRieszEncodeBHist T))
            (frechetRieszDecodeBHist (frechetRieszEncodeBHist C))
            (frechetRieszDecodeBHist (frechetRieszEncodeBHist Q))
            (frechetRieszDecodeBHist (frechetRieszEncodeBHist N))) =
          some (FrechetRieszUp.mk H I L V E K P R T C Q N)
      rw [FrechetRieszTasteGate_single_carrier_alignment_decode H,
        FrechetRieszTasteGate_single_carrier_alignment_decode I,
        FrechetRieszTasteGate_single_carrier_alignment_decode L,
        FrechetRieszTasteGate_single_carrier_alignment_decode V,
        FrechetRieszTasteGate_single_carrier_alignment_decode E,
        FrechetRieszTasteGate_single_carrier_alignment_decode K,
        FrechetRieszTasteGate_single_carrier_alignment_decode P,
        FrechetRieszTasteGate_single_carrier_alignment_decode R,
        FrechetRieszTasteGate_single_carrier_alignment_decode T,
        FrechetRieszTasteGate_single_carrier_alignment_decode C,
        FrechetRieszTasteGate_single_carrier_alignment_decode Q,
        FrechetRieszTasteGate_single_carrier_alignment_decode N]

private theorem FrechetRieszTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FrechetRieszUp} :
    frechetRieszToEventFlow x = frechetRieszToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      frechetRieszFromEventFlow (frechetRieszToEventFlow x) =
        frechetRieszFromEventFlow (frechetRieszToEventFlow y) :=
    congrArg frechetRieszFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FrechetRieszTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FrechetRieszTasteGate_single_carrier_alignment_round_trip y)))

instance frechetRieszBHistCarrier : BHistCarrier FrechetRieszUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := frechetRieszToEventFlow
  fromEventFlow := frechetRieszFromEventFlow

instance frechetRieszChapterTasteGate : ChapterTasteGate FrechetRieszUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change frechetRieszFromEventFlow (frechetRieszToEventFlow x) = some x
    exact FrechetRieszTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FrechetRieszTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate FrechetRieszUp :=
  -- BEDC touchpoint anchor: BHist BMark
  frechetRieszChapterTasteGate

theorem FrechetRieszTasteGate_single_carrier_alignment :
    (∀ h : BHist, frechetRieszDecodeBHist (frechetRieszEncodeBHist h) = h) ∧
      (∀ x : FrechetRieszUp, frechetRieszFromEventFlow (frechetRieszToEventFlow x) = some x) ∧
        (∀ x y : FrechetRieszUp, frechetRieszToEventFlow x = frechetRieszToEventFlow y → x = y) ∧
          frechetRieszEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨FrechetRieszTasteGate_single_carrier_alignment_decode,
      FrechetRieszTasteGate_single_carrier_alignment_round_trip,
      fun x y heq => FrechetRieszTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.FrechetRieszUp
