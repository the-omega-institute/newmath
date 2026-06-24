import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteDyadicBisectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteDyadicBisectionUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (I D M L R S Q E H C P N : BHist) : FiniteDyadicBisectionUp
  deriving DecidableEq

def finiteDyadicBisectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteDyadicBisectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteDyadicBisectionEncodeBHist h

def finiteDyadicBisectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteDyadicBisectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteDyadicBisectionDecodeBHist tail)

private theorem FiniteDyadicBisectionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteDyadicBisectionFields : FiniteDyadicBisectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteDyadicBisectionUp.mk I D M L R S Q E H C P N =>
      [I, D, M, L, R, S, Q, E, H, C, P, N]

def finiteDyadicBisectionToEventFlow : FiniteDyadicBisectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteDyadicBisectionFields x).map finiteDyadicBisectionEncodeBHist

private def finiteDyadicBisectionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteDyadicBisectionEventAt index rest

def finiteDyadicBisectionFromEventFlow (ef : EventFlow) : Option FiniteDyadicBisectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteDyadicBisectionUp.mk
      (finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEventAt 0 ef))
      (finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEventAt 1 ef))
      (finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEventAt 2 ef))
      (finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEventAt 3 ef))
      (finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEventAt 4 ef))
      (finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEventAt 5 ef))
      (finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEventAt 6 ef))
      (finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEventAt 7 ef))
      (finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEventAt 8 ef))
      (finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEventAt 9 ef))
      (finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEventAt 10 ef))
      (finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEventAt 11 ef)))

private theorem FiniteDyadicBisectionTasteGate_single_carrier_alignment_round_trip
    (x : FiniteDyadicBisectionUp) :
    finiteDyadicBisectionFromEventFlow (finiteDyadicBisectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I D M L R S Q E H C P N =>
      change
        some
          (FiniteDyadicBisectionUp.mk
            (finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEncodeBHist I))
            (finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEncodeBHist D))
            (finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEncodeBHist M))
            (finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEncodeBHist L))
            (finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEncodeBHist R))
            (finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEncodeBHist S))
            (finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEncodeBHist Q))
            (finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEncodeBHist E))
            (finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEncodeBHist H))
            (finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEncodeBHist C))
            (finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEncodeBHist P))
            (finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEncodeBHist N))) =
          some (FiniteDyadicBisectionUp.mk I D M L R S Q E H C P N)
      rw [FiniteDyadicBisectionTasteGate_single_carrier_alignment_decode I,
        FiniteDyadicBisectionTasteGate_single_carrier_alignment_decode D,
        FiniteDyadicBisectionTasteGate_single_carrier_alignment_decode M,
        FiniteDyadicBisectionTasteGate_single_carrier_alignment_decode L,
        FiniteDyadicBisectionTasteGate_single_carrier_alignment_decode R,
        FiniteDyadicBisectionTasteGate_single_carrier_alignment_decode S,
        FiniteDyadicBisectionTasteGate_single_carrier_alignment_decode Q,
        FiniteDyadicBisectionTasteGate_single_carrier_alignment_decode E,
        FiniteDyadicBisectionTasteGate_single_carrier_alignment_decode H,
        FiniteDyadicBisectionTasteGate_single_carrier_alignment_decode C,
        FiniteDyadicBisectionTasteGate_single_carrier_alignment_decode P,
        FiniteDyadicBisectionTasteGate_single_carrier_alignment_decode N]

private theorem FiniteDyadicBisectionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteDyadicBisectionUp} :
    finiteDyadicBisectionToEventFlow x = finiteDyadicBisectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteDyadicBisectionFromEventFlow (finiteDyadicBisectionToEventFlow x) =
        finiteDyadicBisectionFromEventFlow (finiteDyadicBisectionToEventFlow y) :=
    congrArg finiteDyadicBisectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteDyadicBisectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteDyadicBisectionTasteGate_single_carrier_alignment_round_trip y)))

instance finiteDyadicBisectionBHistCarrier : BHistCarrier FiniteDyadicBisectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteDyadicBisectionToEventFlow
  fromEventFlow := finiteDyadicBisectionFromEventFlow

instance finiteDyadicBisectionChapterTasteGate : ChapterTasteGate FiniteDyadicBisectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteDyadicBisectionFromEventFlow (finiteDyadicBisectionToEventFlow x) = some x
    exact FiniteDyadicBisectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteDyadicBisectionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate FiniteDyadicBisectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteDyadicBisectionChapterTasteGate

theorem FiniteDyadicBisectionTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteDyadicBisectionDecodeBHist (finiteDyadicBisectionEncodeBHist h) = h) ∧
      Nonempty (ChapterTasteGate FiniteDyadicBisectionUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FiniteDyadicBisectionTasteGate_single_carrier_alignment_decode,
      ⟨finiteDyadicBisectionChapterTasteGate⟩⟩

end BEDC.Derived.FiniteDyadicBisectionUp
