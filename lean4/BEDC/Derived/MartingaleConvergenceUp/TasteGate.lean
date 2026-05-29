import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MartingaleConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MartingaleConvergenceUp : Type where
  | mk (Omega X E M T O U D S R L A H K P N : BHist) : MartingaleConvergenceUp
  deriving DecidableEq

def martingaleConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: martingaleConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: martingaleConvergenceEncodeBHist h

def martingaleConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (martingaleConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (martingaleConvergenceDecodeBHist tail)

private theorem martingaleConvergence_decode_encode :
    ∀ h : BHist, martingaleConvergenceDecodeBHist (martingaleConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def martingaleConvergenceFields : MartingaleConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MartingaleConvergenceUp.mk Omega X E M T O U D S R L A H K P N =>
      [Omega, X, E, M, T, O, U, D, S, R, L, A, H, K, P, N]

def martingaleConvergenceToEventFlow : MartingaleConvergenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (martingaleConvergenceFields x).map martingaleConvergenceEncodeBHist

private def martingaleConvergenceDecodePacket
    (Omega X E M T O U D S R L A H K P N : RawEvent) : MartingaleConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  MartingaleConvergenceUp.mk
    (martingaleConvergenceDecodeBHist Omega)
    (martingaleConvergenceDecodeBHist X)
    (martingaleConvergenceDecodeBHist E)
    (martingaleConvergenceDecodeBHist M)
    (martingaleConvergenceDecodeBHist T)
    (martingaleConvergenceDecodeBHist O)
    (martingaleConvergenceDecodeBHist U)
    (martingaleConvergenceDecodeBHist D)
    (martingaleConvergenceDecodeBHist S)
    (martingaleConvergenceDecodeBHist R)
    (martingaleConvergenceDecodeBHist L)
    (martingaleConvergenceDecodeBHist A)
    (martingaleConvergenceDecodeBHist H)
    (martingaleConvergenceDecodeBHist K)
    (martingaleConvergenceDecodeBHist P)
    (martingaleConvergenceDecodeBHist N)

private def martingaleConvergenceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => martingaleConvergenceRawAt n rest

private def martingaleConvergenceLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => martingaleConvergenceLengthEq n rest

def martingaleConvergenceFromEventFlow (flow : EventFlow) : Option MartingaleConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match martingaleConvergenceLengthEq 16 flow with
  | true =>
      some
        (martingaleConvergenceDecodePacket
          (martingaleConvergenceRawAt 0 flow)
          (martingaleConvergenceRawAt 1 flow)
          (martingaleConvergenceRawAt 2 flow)
          (martingaleConvergenceRawAt 3 flow)
          (martingaleConvergenceRawAt 4 flow)
          (martingaleConvergenceRawAt 5 flow)
          (martingaleConvergenceRawAt 6 flow)
          (martingaleConvergenceRawAt 7 flow)
          (martingaleConvergenceRawAt 8 flow)
          (martingaleConvergenceRawAt 9 flow)
          (martingaleConvergenceRawAt 10 flow)
          (martingaleConvergenceRawAt 11 flow)
          (martingaleConvergenceRawAt 12 flow)
          (martingaleConvergenceRawAt 13 flow)
          (martingaleConvergenceRawAt 14 flow)
          (martingaleConvergenceRawAt 15 flow))
  | false => none

private theorem martingaleConvergence_round_trip :
    ∀ x : MartingaleConvergenceUp,
      martingaleConvergenceFromEventFlow (martingaleConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Omega X E M T O U D S R L A H K P N =>
      change
        some
          (martingaleConvergenceDecodePacket
            (martingaleConvergenceEncodeBHist Omega)
            (martingaleConvergenceEncodeBHist X)
            (martingaleConvergenceEncodeBHist E)
            (martingaleConvergenceEncodeBHist M)
            (martingaleConvergenceEncodeBHist T)
            (martingaleConvergenceEncodeBHist O)
            (martingaleConvergenceEncodeBHist U)
            (martingaleConvergenceEncodeBHist D)
            (martingaleConvergenceEncodeBHist S)
            (martingaleConvergenceEncodeBHist R)
            (martingaleConvergenceEncodeBHist L)
            (martingaleConvergenceEncodeBHist A)
            (martingaleConvergenceEncodeBHist H)
            (martingaleConvergenceEncodeBHist K)
            (martingaleConvergenceEncodeBHist P)
            (martingaleConvergenceEncodeBHist N)) =
          some (MartingaleConvergenceUp.mk Omega X E M T O U D S R L A H K P N)
      unfold martingaleConvergenceDecodePacket
      rw [martingaleConvergence_decode_encode Omega,
        martingaleConvergence_decode_encode X,
        martingaleConvergence_decode_encode E,
        martingaleConvergence_decode_encode M,
        martingaleConvergence_decode_encode T,
        martingaleConvergence_decode_encode O,
        martingaleConvergence_decode_encode U,
        martingaleConvergence_decode_encode D,
        martingaleConvergence_decode_encode S,
        martingaleConvergence_decode_encode R,
        martingaleConvergence_decode_encode L,
        martingaleConvergence_decode_encode A,
        martingaleConvergence_decode_encode H,
        martingaleConvergence_decode_encode K,
        martingaleConvergence_decode_encode P,
        martingaleConvergence_decode_encode N]

private theorem martingaleConvergenceToEventFlow_injective {x y : MartingaleConvergenceUp} :
    martingaleConvergenceToEventFlow x = martingaleConvergenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      martingaleConvergenceFromEventFlow (martingaleConvergenceToEventFlow x) =
        martingaleConvergenceFromEventFlow (martingaleConvergenceToEventFlow y) :=
    congrArg martingaleConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (martingaleConvergence_round_trip x).symm
      (Eq.trans hread (martingaleConvergence_round_trip y)))

instance martingaleConvergenceBHistCarrier : BHistCarrier MartingaleConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := martingaleConvergenceToEventFlow
  fromEventFlow := martingaleConvergenceFromEventFlow

instance martingaleConvergenceChapterTasteGate : ChapterTasteGate MartingaleConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change martingaleConvergenceFromEventFlow (martingaleConvergenceToEventFlow x) = some x
    exact martingaleConvergence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (martingaleConvergenceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate MartingaleConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  martingaleConvergenceChapterTasteGate

theorem MartingaleConvergenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, martingaleConvergenceDecodeBHist (martingaleConvergenceEncodeBHist h) = h) ∧
      (∀ x : MartingaleConvergenceUp,
        martingaleConvergenceFromEventFlow (martingaleConvergenceToEventFlow x) = some x) ∧
        (∀ x y : MartingaleConvergenceUp,
          martingaleConvergenceToEventFlow x = martingaleConvergenceToEventFlow y → x = y) ∧
          martingaleConvergenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨martingaleConvergence_decode_encode,
      martingaleConvergence_round_trip,
      fun _ _ heq => martingaleConvergenceToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.MartingaleConvergenceUp
