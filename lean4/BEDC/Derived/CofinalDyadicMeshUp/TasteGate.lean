import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CofinalDyadicMeshUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CofinalDyadicMeshUp : Type where
  | mk : (Q D M S R E H C P N : BHist) → CofinalDyadicMeshUp
  deriving DecidableEq

def cofinalDyadicMeshEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cofinalDyadicMeshEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cofinalDyadicMeshEncodeBHist h

def cofinalDyadicMeshDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cofinalDyadicMeshDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cofinalDyadicMeshDecodeBHist tail)

private theorem cofinalDyadicMesh_decode_encode :
    ∀ h : BHist, cofinalDyadicMeshDecodeBHist (cofinalDyadicMeshEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cofinalDyadicMeshFields : CofinalDyadicMeshUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CofinalDyadicMeshUp.mk Q D M S R E H C P N => [Q, D, M, S, R, E, H, C, P, N]

def cofinalDyadicMeshToEventFlow : CofinalDyadicMeshUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cofinalDyadicMeshFields x).map cofinalDyadicMeshEncodeBHist

private def cofinalDyadicMeshEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cofinalDyadicMeshEventAt index rest

def cofinalDyadicMeshFromEventFlow (ef : EventFlow) : Option CofinalDyadicMeshUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CofinalDyadicMeshUp.mk
      (cofinalDyadicMeshDecodeBHist (cofinalDyadicMeshEventAt 0 ef))
      (cofinalDyadicMeshDecodeBHist (cofinalDyadicMeshEventAt 1 ef))
      (cofinalDyadicMeshDecodeBHist (cofinalDyadicMeshEventAt 2 ef))
      (cofinalDyadicMeshDecodeBHist (cofinalDyadicMeshEventAt 3 ef))
      (cofinalDyadicMeshDecodeBHist (cofinalDyadicMeshEventAt 4 ef))
      (cofinalDyadicMeshDecodeBHist (cofinalDyadicMeshEventAt 5 ef))
      (cofinalDyadicMeshDecodeBHist (cofinalDyadicMeshEventAt 6 ef))
      (cofinalDyadicMeshDecodeBHist (cofinalDyadicMeshEventAt 7 ef))
      (cofinalDyadicMeshDecodeBHist (cofinalDyadicMeshEventAt 8 ef))
      (cofinalDyadicMeshDecodeBHist (cofinalDyadicMeshEventAt 9 ef)))

private theorem cofinalDyadicMesh_round_trip :
    ∀ x : CofinalDyadicMeshUp,
      cofinalDyadicMeshFromEventFlow (cofinalDyadicMeshToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q D M S R E H C P N =>
      change
        some
            (CofinalDyadicMeshUp.mk
              (cofinalDyadicMeshDecodeBHist (cofinalDyadicMeshEncodeBHist Q))
              (cofinalDyadicMeshDecodeBHist (cofinalDyadicMeshEncodeBHist D))
              (cofinalDyadicMeshDecodeBHist (cofinalDyadicMeshEncodeBHist M))
              (cofinalDyadicMeshDecodeBHist (cofinalDyadicMeshEncodeBHist S))
              (cofinalDyadicMeshDecodeBHist (cofinalDyadicMeshEncodeBHist R))
              (cofinalDyadicMeshDecodeBHist (cofinalDyadicMeshEncodeBHist E))
              (cofinalDyadicMeshDecodeBHist (cofinalDyadicMeshEncodeBHist H))
              (cofinalDyadicMeshDecodeBHist (cofinalDyadicMeshEncodeBHist C))
              (cofinalDyadicMeshDecodeBHist (cofinalDyadicMeshEncodeBHist P))
              (cofinalDyadicMeshDecodeBHist (cofinalDyadicMeshEncodeBHist N))) =
          some (CofinalDyadicMeshUp.mk Q D M S R E H C P N)
      rw [cofinalDyadicMesh_decode_encode Q]
      rw [cofinalDyadicMesh_decode_encode D]
      rw [cofinalDyadicMesh_decode_encode M]
      rw [cofinalDyadicMesh_decode_encode S]
      rw [cofinalDyadicMesh_decode_encode R]
      rw [cofinalDyadicMesh_decode_encode E]
      rw [cofinalDyadicMesh_decode_encode H]
      rw [cofinalDyadicMesh_decode_encode C]
      rw [cofinalDyadicMesh_decode_encode P]
      rw [cofinalDyadicMesh_decode_encode N]

private theorem cofinalDyadicMeshToEventFlow_injective {x y : CofinalDyadicMeshUp} :
    cofinalDyadicMeshToEventFlow x = cofinalDyadicMeshToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hread :
      cofinalDyadicMeshFromEventFlow (cofinalDyadicMeshToEventFlow x) =
        cofinalDyadicMeshFromEventFlow (cofinalDyadicMeshToEventFlow y) :=
    congrArg cofinalDyadicMeshFromEventFlow hxy
  exact Option.some.inj
    (Eq.trans (cofinalDyadicMesh_round_trip x).symm
      (Eq.trans hread (cofinalDyadicMesh_round_trip y)))

instance cofinalDyadicMeshBHistCarrier : BHistCarrier CofinalDyadicMeshUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cofinalDyadicMeshToEventFlow
  fromEventFlow := cofinalDyadicMeshFromEventFlow

instance cofinalDyadicMeshChapterTasteGate : ChapterTasteGate CofinalDyadicMeshUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cofinalDyadicMeshFromEventFlow (cofinalDyadicMeshToEventFlow x) = some x
    exact cofinalDyadicMesh_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cofinalDyadicMeshToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CofinalDyadicMeshUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cofinalDyadicMeshChapterTasteGate

theorem CofinalDyadicMeshTasteGate_single_carrier_alignment :
    (∀ h : BHist, cofinalDyadicMeshDecodeBHist (cofinalDyadicMeshEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CofinalDyadicMeshUp) ∧
        Nonempty (ChapterTasteGate CofinalDyadicMeshUp) ∧
          cofinalDyadicMeshEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cofinalDyadicMesh_decode_encode
  · constructor
    · exact ⟨cofinalDyadicMeshBHistCarrier⟩
    · constructor
      · exact ⟨cofinalDyadicMeshChapterTasteGate⟩
      · rfl

end BEDC.Derived.CofinalDyadicMeshUp
