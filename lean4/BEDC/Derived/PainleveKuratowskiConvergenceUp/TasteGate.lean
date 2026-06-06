import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PainleveKuratowskiConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PainleveKuratowskiConvergenceUp : Type where
  | mk (L U K H V W R E T C P N : BHist) : PainleveKuratowskiConvergenceUp
  deriving DecidableEq

def painleveKuratowskiConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: painleveKuratowskiConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: painleveKuratowskiConvergenceEncodeBHist h

def painleveKuratowskiConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (painleveKuratowskiConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (painleveKuratowskiConvergenceDecodeBHist tail)

private theorem painleveKuratowskiConvergenceDecodeEncode :
    ∀ h : BHist,
      painleveKuratowskiConvergenceDecodeBHist
        (painleveKuratowskiConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def painleveKuratowskiConvergenceFields :
    PainleveKuratowskiConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PainleveKuratowskiConvergenceUp.mk L U K H V W R E T C P N =>
      [L, U, K, H, V, W, R, E, T, C, P, N]

def painleveKuratowskiConvergenceToEventFlow :
    PainleveKuratowskiConvergenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (painleveKuratowskiConvergenceFields x).map
      painleveKuratowskiConvergenceEncodeBHist

private def painleveKuratowskiConvergenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => painleveKuratowskiConvergenceEventAt index rest

def painleveKuratowskiConvergenceFromEventFlow
    (flow : EventFlow) : Option PainleveKuratowskiConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PainleveKuratowskiConvergenceUp.mk
      (painleveKuratowskiConvergenceDecodeBHist
        (painleveKuratowskiConvergenceEventAt 0 flow))
      (painleveKuratowskiConvergenceDecodeBHist
        (painleveKuratowskiConvergenceEventAt 1 flow))
      (painleveKuratowskiConvergenceDecodeBHist
        (painleveKuratowskiConvergenceEventAt 2 flow))
      (painleveKuratowskiConvergenceDecodeBHist
        (painleveKuratowskiConvergenceEventAt 3 flow))
      (painleveKuratowskiConvergenceDecodeBHist
        (painleveKuratowskiConvergenceEventAt 4 flow))
      (painleveKuratowskiConvergenceDecodeBHist
        (painleveKuratowskiConvergenceEventAt 5 flow))
      (painleveKuratowskiConvergenceDecodeBHist
        (painleveKuratowskiConvergenceEventAt 6 flow))
      (painleveKuratowskiConvergenceDecodeBHist
        (painleveKuratowskiConvergenceEventAt 7 flow))
      (painleveKuratowskiConvergenceDecodeBHist
        (painleveKuratowskiConvergenceEventAt 8 flow))
      (painleveKuratowskiConvergenceDecodeBHist
        (painleveKuratowskiConvergenceEventAt 9 flow))
      (painleveKuratowskiConvergenceDecodeBHist
        (painleveKuratowskiConvergenceEventAt 10 flow))
      (painleveKuratowskiConvergenceDecodeBHist
        (painleveKuratowskiConvergenceEventAt 11 flow)))

private theorem painleveKuratowskiConvergenceRoundTrip
    (x : PainleveKuratowskiConvergenceUp) :
    painleveKuratowskiConvergenceFromEventFlow
      (painleveKuratowskiConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L U K H V W R E T C P N =>
      change
        some
          (PainleveKuratowskiConvergenceUp.mk
            (painleveKuratowskiConvergenceDecodeBHist
              (painleveKuratowskiConvergenceEncodeBHist L))
            (painleveKuratowskiConvergenceDecodeBHist
              (painleveKuratowskiConvergenceEncodeBHist U))
            (painleveKuratowskiConvergenceDecodeBHist
              (painleveKuratowskiConvergenceEncodeBHist K))
            (painleveKuratowskiConvergenceDecodeBHist
              (painleveKuratowskiConvergenceEncodeBHist H))
            (painleveKuratowskiConvergenceDecodeBHist
              (painleveKuratowskiConvergenceEncodeBHist V))
            (painleveKuratowskiConvergenceDecodeBHist
              (painleveKuratowskiConvergenceEncodeBHist W))
            (painleveKuratowskiConvergenceDecodeBHist
              (painleveKuratowskiConvergenceEncodeBHist R))
            (painleveKuratowskiConvergenceDecodeBHist
              (painleveKuratowskiConvergenceEncodeBHist E))
            (painleveKuratowskiConvergenceDecodeBHist
              (painleveKuratowskiConvergenceEncodeBHist T))
            (painleveKuratowskiConvergenceDecodeBHist
              (painleveKuratowskiConvergenceEncodeBHist C))
            (painleveKuratowskiConvergenceDecodeBHist
              (painleveKuratowskiConvergenceEncodeBHist P))
            (painleveKuratowskiConvergenceDecodeBHist
              (painleveKuratowskiConvergenceEncodeBHist N))) =
          some (PainleveKuratowskiConvergenceUp.mk L U K H V W R E T C P N)
      rw [painleveKuratowskiConvergenceDecodeEncode L,
        painleveKuratowskiConvergenceDecodeEncode U,
        painleveKuratowskiConvergenceDecodeEncode K,
        painleveKuratowskiConvergenceDecodeEncode H,
        painleveKuratowskiConvergenceDecodeEncode V,
        painleveKuratowskiConvergenceDecodeEncode W,
        painleveKuratowskiConvergenceDecodeEncode R,
        painleveKuratowskiConvergenceDecodeEncode E,
        painleveKuratowskiConvergenceDecodeEncode T,
        painleveKuratowskiConvergenceDecodeEncode C,
        painleveKuratowskiConvergenceDecodeEncode P,
        painleveKuratowskiConvergenceDecodeEncode N]

private theorem painleveKuratowskiConvergenceToEventFlow_injective
    {x y : PainleveKuratowskiConvergenceUp} :
    painleveKuratowskiConvergenceToEventFlow x =
        painleveKuratowskiConvergenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      painleveKuratowskiConvergenceFromEventFlow
          (painleveKuratowskiConvergenceToEventFlow x) =
        painleveKuratowskiConvergenceFromEventFlow
          (painleveKuratowskiConvergenceToEventFlow y) :=
    congrArg painleveKuratowskiConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (painleveKuratowskiConvergenceRoundTrip x).symm
      (Eq.trans hread (painleveKuratowskiConvergenceRoundTrip y)))

instance painleveKuratowskiConvergenceBHistCarrier :
    BHistCarrier PainleveKuratowskiConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := painleveKuratowskiConvergenceToEventFlow
  fromEventFlow := painleveKuratowskiConvergenceFromEventFlow

instance painleveKuratowskiConvergenceChapterTasteGate :
    ChapterTasteGate PainleveKuratowskiConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      painleveKuratowskiConvergenceFromEventFlow
        (painleveKuratowskiConvergenceToEventFlow x) = some x
    exact painleveKuratowskiConvergenceRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (painleveKuratowskiConvergenceToEventFlow_injective heq)

theorem PainleveKuratowskiConvergenceTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier PainleveKuratowskiConvergenceUp) ∧
      Nonempty (ChapterTasteGate PainleveKuratowskiConvergenceUp) ∧
        (∀ x : PainleveKuratowskiConvergenceUp,
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
          (∃ x : PainleveKuratowskiConvergenceUp,
            List.Mem ([] : RawEvent) (BHistCarrier.toEventFlow x)) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  refine
    ⟨⟨painleveKuratowskiConvergenceBHistCarrier⟩,
      ⟨painleveKuratowskiConvergenceChapterTasteGate⟩, ?_, ?_⟩
  · intro x
    change
      painleveKuratowskiConvergenceFromEventFlow
        (painleveKuratowskiConvergenceToEventFlow x) = some x
    exact painleveKuratowskiConvergenceRoundTrip x
  · exact
      ⟨PainleveKuratowskiConvergenceUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty, by
          simp only [BHistCarrier.toEventFlow, painleveKuratowskiConvergenceToEventFlow,
            painleveKuratowskiConvergenceFields]
          exact List.Mem.head _⟩

end BEDC.Derived.PainleveKuratowskiConvergenceUp
