import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformBoundednessPrincipleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformBoundednessPrincipleUp : Type where
  | mk (B F W L R H C P N : BHist) : UniformBoundednessPrincipleUp
  deriving DecidableEq

def uniformBoundednessPrincipleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformBoundednessPrincipleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformBoundednessPrincipleEncodeBHist h

def uniformBoundednessPrincipleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformBoundednessPrincipleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformBoundednessPrincipleDecodeBHist tail)

private theorem UniformBoundednessPrincipleTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      uniformBoundednessPrincipleDecodeBHist
        (uniformBoundednessPrincipleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformBoundednessPrincipleFields : UniformBoundednessPrincipleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformBoundednessPrincipleUp.mk B F W L R H C P N => [B, F, W, L, R, H, C, P, N]

def uniformBoundednessPrincipleToEventFlow :
    UniformBoundednessPrincipleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformBoundednessPrincipleFields x).map uniformBoundednessPrincipleEncodeBHist

private def UniformBoundednessPrincipleTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      UniformBoundednessPrincipleTasteGate_single_carrier_alignment_eventAt index rest

def uniformBoundednessPrincipleFromEventFlow
    (ef : EventFlow) : Option UniformBoundednessPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformBoundednessPrincipleUp.mk
      (uniformBoundednessPrincipleDecodeBHist
        (UniformBoundednessPrincipleTasteGate_single_carrier_alignment_eventAt 0 ef))
      (uniformBoundednessPrincipleDecodeBHist
        (UniformBoundednessPrincipleTasteGate_single_carrier_alignment_eventAt 1 ef))
      (uniformBoundednessPrincipleDecodeBHist
        (UniformBoundednessPrincipleTasteGate_single_carrier_alignment_eventAt 2 ef))
      (uniformBoundednessPrincipleDecodeBHist
        (UniformBoundednessPrincipleTasteGate_single_carrier_alignment_eventAt 3 ef))
      (uniformBoundednessPrincipleDecodeBHist
        (UniformBoundednessPrincipleTasteGate_single_carrier_alignment_eventAt 4 ef))
      (uniformBoundednessPrincipleDecodeBHist
        (UniformBoundednessPrincipleTasteGate_single_carrier_alignment_eventAt 5 ef))
      (uniformBoundednessPrincipleDecodeBHist
        (UniformBoundednessPrincipleTasteGate_single_carrier_alignment_eventAt 6 ef))
      (uniformBoundednessPrincipleDecodeBHist
        (UniformBoundednessPrincipleTasteGate_single_carrier_alignment_eventAt 7 ef))
      (uniformBoundednessPrincipleDecodeBHist
        (UniformBoundednessPrincipleTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem UniformBoundednessPrincipleTasteGate_single_carrier_alignment_round_trip
    (x : UniformBoundednessPrincipleUp) :
    uniformBoundednessPrincipleFromEventFlow
      (uniformBoundednessPrincipleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B F W L R H C P N =>
      change
        some
          (UniformBoundednessPrincipleUp.mk
            (uniformBoundednessPrincipleDecodeBHist
              (uniformBoundednessPrincipleEncodeBHist B))
            (uniformBoundednessPrincipleDecodeBHist
              (uniformBoundednessPrincipleEncodeBHist F))
            (uniformBoundednessPrincipleDecodeBHist
              (uniformBoundednessPrincipleEncodeBHist W))
            (uniformBoundednessPrincipleDecodeBHist
              (uniformBoundednessPrincipleEncodeBHist L))
            (uniformBoundednessPrincipleDecodeBHist
              (uniformBoundednessPrincipleEncodeBHist R))
            (uniformBoundednessPrincipleDecodeBHist
              (uniformBoundednessPrincipleEncodeBHist H))
            (uniformBoundednessPrincipleDecodeBHist
              (uniformBoundednessPrincipleEncodeBHist C))
            (uniformBoundednessPrincipleDecodeBHist
              (uniformBoundednessPrincipleEncodeBHist P))
            (uniformBoundednessPrincipleDecodeBHist
              (uniformBoundednessPrincipleEncodeBHist N))) =
          some (UniformBoundednessPrincipleUp.mk B F W L R H C P N)
      rw [UniformBoundednessPrincipleTasteGate_single_carrier_alignment_decode_encode B,
        UniformBoundednessPrincipleTasteGate_single_carrier_alignment_decode_encode F,
        UniformBoundednessPrincipleTasteGate_single_carrier_alignment_decode_encode W,
        UniformBoundednessPrincipleTasteGate_single_carrier_alignment_decode_encode L,
        UniformBoundednessPrincipleTasteGate_single_carrier_alignment_decode_encode R,
        UniformBoundednessPrincipleTasteGate_single_carrier_alignment_decode_encode H,
        UniformBoundednessPrincipleTasteGate_single_carrier_alignment_decode_encode C,
        UniformBoundednessPrincipleTasteGate_single_carrier_alignment_decode_encode P,
        UniformBoundednessPrincipleTasteGate_single_carrier_alignment_decode_encode N]

private theorem UniformBoundednessPrincipleTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformBoundednessPrincipleUp} :
    uniformBoundednessPrincipleToEventFlow x =
      uniformBoundednessPrincipleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformBoundednessPrincipleFromEventFlow
          (uniformBoundednessPrincipleToEventFlow x) =
        uniformBoundednessPrincipleFromEventFlow
          (uniformBoundednessPrincipleToEventFlow y) :=
    congrArg uniformBoundednessPrincipleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformBoundednessPrincipleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (UniformBoundednessPrincipleTasteGate_single_carrier_alignment_round_trip y)))

instance uniformBoundednessPrincipleBHistCarrier :
    BHistCarrier UniformBoundednessPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformBoundednessPrincipleToEventFlow
  fromEventFlow := uniformBoundednessPrincipleFromEventFlow

instance uniformBoundednessPrincipleChapterTasteGate :
    ChapterTasteGate UniformBoundednessPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformBoundednessPrincipleFromEventFlow
        (uniformBoundednessPrincipleToEventFlow x) = some x
    exact UniformBoundednessPrincipleTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (UniformBoundednessPrincipleTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem UniformBoundednessPrincipleTasteGate_single_carrier_alignment :
    (uniformBoundednessPrincipleEncodeBHist BHist.Empty = ([] : RawEvent)) ∧
      (uniformBoundednessPrincipleDecodeBHist [BMark.b1] = BHist.e1 BHist.Empty) ∧
        (∀ h : BHist,
          uniformBoundednessPrincipleDecodeBHist
            (uniformBoundednessPrincipleEncodeBHist h) = h) ∧
          Nonempty (BHistCarrier UniformBoundednessPrincipleUp) ∧
            Nonempty (ChapterTasteGate UniformBoundednessPrincipleUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨rfl, rfl, UniformBoundednessPrincipleTasteGate_single_carrier_alignment_decode_encode,
      ⟨uniformBoundednessPrincipleBHistCarrier⟩,
      ⟨uniformBoundednessPrincipleChapterTasteGate⟩⟩

end BEDC.Derived.UniformBoundednessPrincipleUp
