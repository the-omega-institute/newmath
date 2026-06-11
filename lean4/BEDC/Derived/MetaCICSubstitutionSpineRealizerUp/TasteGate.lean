import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICSubstitutionSpineRealizerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICSubstitutionSpineRealizerUp : Type where
  | mk
      (term index binderSeal closedShift closedSubstitution closedComposition handoff ledger
        transport replay provenance name : BHist) : MetaCICSubstitutionSpineRealizerUp
  deriving DecidableEq

def metacicSubstitutionSpineRealizerEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metacicSubstitutionSpineRealizerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metacicSubstitutionSpineRealizerEncodeBHist h

def metacicSubstitutionSpineRealizerDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metacicSubstitutionSpineRealizerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metacicSubstitutionSpineRealizerDecodeBHist tail)

private theorem MetaCICSubstitutionSpineRealizerTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      metacicSubstitutionSpineRealizerDecodeBHist
          (metacicSubstitutionSpineRealizerEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metacicSubstitutionSpineRealizerToEventFlow :
    MetaCICSubstitutionSpineRealizerUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICSubstitutionSpineRealizerUp.mk term index binderSeal closedShift
      closedSubstitution closedComposition handoff ledger transport replay provenance name =>
      [metacicSubstitutionSpineRealizerEncodeBHist term,
        metacicSubstitutionSpineRealizerEncodeBHist index,
        metacicSubstitutionSpineRealizerEncodeBHist binderSeal,
        metacicSubstitutionSpineRealizerEncodeBHist closedShift,
        metacicSubstitutionSpineRealizerEncodeBHist closedSubstitution,
        metacicSubstitutionSpineRealizerEncodeBHist closedComposition,
        metacicSubstitutionSpineRealizerEncodeBHist handoff,
        metacicSubstitutionSpineRealizerEncodeBHist ledger,
        metacicSubstitutionSpineRealizerEncodeBHist transport,
        metacicSubstitutionSpineRealizerEncodeBHist replay,
        metacicSubstitutionSpineRealizerEncodeBHist provenance,
        metacicSubstitutionSpineRealizerEncodeBHist name]

private def metacicSubstitutionSpineRealizerEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      metacicSubstitutionSpineRealizerEventAtDefault index rest

def metacicSubstitutionSpineRealizerFromEventFlow
    (ef : EventFlow) : Option MetaCICSubstitutionSpineRealizerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetaCICSubstitutionSpineRealizerUp.mk
      (metacicSubstitutionSpineRealizerDecodeBHist
        (metacicSubstitutionSpineRealizerEventAtDefault 0 ef))
      (metacicSubstitutionSpineRealizerDecodeBHist
        (metacicSubstitutionSpineRealizerEventAtDefault 1 ef))
      (metacicSubstitutionSpineRealizerDecodeBHist
        (metacicSubstitutionSpineRealizerEventAtDefault 2 ef))
      (metacicSubstitutionSpineRealizerDecodeBHist
        (metacicSubstitutionSpineRealizerEventAtDefault 3 ef))
      (metacicSubstitutionSpineRealizerDecodeBHist
        (metacicSubstitutionSpineRealizerEventAtDefault 4 ef))
      (metacicSubstitutionSpineRealizerDecodeBHist
        (metacicSubstitutionSpineRealizerEventAtDefault 5 ef))
      (metacicSubstitutionSpineRealizerDecodeBHist
        (metacicSubstitutionSpineRealizerEventAtDefault 6 ef))
      (metacicSubstitutionSpineRealizerDecodeBHist
        (metacicSubstitutionSpineRealizerEventAtDefault 7 ef))
      (metacicSubstitutionSpineRealizerDecodeBHist
        (metacicSubstitutionSpineRealizerEventAtDefault 8 ef))
      (metacicSubstitutionSpineRealizerDecodeBHist
        (metacicSubstitutionSpineRealizerEventAtDefault 9 ef))
      (metacicSubstitutionSpineRealizerDecodeBHist
        (metacicSubstitutionSpineRealizerEventAtDefault 10 ef))
      (metacicSubstitutionSpineRealizerDecodeBHist
        (metacicSubstitutionSpineRealizerEventAtDefault 11 ef)))

private theorem MetaCICSubstitutionSpineRealizerTasteGate_single_carrier_alignment_round_trip
    (x : MetaCICSubstitutionSpineRealizerUp) :
    metacicSubstitutionSpineRealizerFromEventFlow
        (metacicSubstitutionSpineRealizerToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk term index binderSeal closedShift closedSubstitution closedComposition handoff ledger
      transport replay provenance name =>
      change
        some
          (MetaCICSubstitutionSpineRealizerUp.mk
            (metacicSubstitutionSpineRealizerDecodeBHist
              (metacicSubstitutionSpineRealizerEncodeBHist term))
            (metacicSubstitutionSpineRealizerDecodeBHist
              (metacicSubstitutionSpineRealizerEncodeBHist index))
            (metacicSubstitutionSpineRealizerDecodeBHist
              (metacicSubstitutionSpineRealizerEncodeBHist binderSeal))
            (metacicSubstitutionSpineRealizerDecodeBHist
              (metacicSubstitutionSpineRealizerEncodeBHist closedShift))
            (metacicSubstitutionSpineRealizerDecodeBHist
              (metacicSubstitutionSpineRealizerEncodeBHist closedSubstitution))
            (metacicSubstitutionSpineRealizerDecodeBHist
              (metacicSubstitutionSpineRealizerEncodeBHist closedComposition))
            (metacicSubstitutionSpineRealizerDecodeBHist
              (metacicSubstitutionSpineRealizerEncodeBHist handoff))
            (metacicSubstitutionSpineRealizerDecodeBHist
              (metacicSubstitutionSpineRealizerEncodeBHist ledger))
            (metacicSubstitutionSpineRealizerDecodeBHist
              (metacicSubstitutionSpineRealizerEncodeBHist transport))
            (metacicSubstitutionSpineRealizerDecodeBHist
              (metacicSubstitutionSpineRealizerEncodeBHist replay))
            (metacicSubstitutionSpineRealizerDecodeBHist
              (metacicSubstitutionSpineRealizerEncodeBHist provenance))
            (metacicSubstitutionSpineRealizerDecodeBHist
              (metacicSubstitutionSpineRealizerEncodeBHist name))) =
          some
            (MetaCICSubstitutionSpineRealizerUp.mk term index binderSeal closedShift
              closedSubstitution closedComposition handoff ledger transport replay provenance name)
      rw [MetaCICSubstitutionSpineRealizerTasteGate_single_carrier_alignment_decode_encode term,
        MetaCICSubstitutionSpineRealizerTasteGate_single_carrier_alignment_decode_encode index,
        MetaCICSubstitutionSpineRealizerTasteGate_single_carrier_alignment_decode_encode binderSeal,
        MetaCICSubstitutionSpineRealizerTasteGate_single_carrier_alignment_decode_encode closedShift,
        MetaCICSubstitutionSpineRealizerTasteGate_single_carrier_alignment_decode_encode
          closedSubstitution,
        MetaCICSubstitutionSpineRealizerTasteGate_single_carrier_alignment_decode_encode
          closedComposition,
        MetaCICSubstitutionSpineRealizerTasteGate_single_carrier_alignment_decode_encode handoff,
        MetaCICSubstitutionSpineRealizerTasteGate_single_carrier_alignment_decode_encode ledger,
        MetaCICSubstitutionSpineRealizerTasteGate_single_carrier_alignment_decode_encode transport,
        MetaCICSubstitutionSpineRealizerTasteGate_single_carrier_alignment_decode_encode replay,
        MetaCICSubstitutionSpineRealizerTasteGate_single_carrier_alignment_decode_encode provenance,
        MetaCICSubstitutionSpineRealizerTasteGate_single_carrier_alignment_decode_encode name]

private theorem MetaCICSubstitutionSpineRealizerTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetaCICSubstitutionSpineRealizerUp} :
    metacicSubstitutionSpineRealizerToEventFlow x =
        metacicSubstitutionSpineRealizerToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metacicSubstitutionSpineRealizerFromEventFlow
          (metacicSubstitutionSpineRealizerToEventFlow x) =
        metacicSubstitutionSpineRealizerFromEventFlow
          (metacicSubstitutionSpineRealizerToEventFlow y) :=
    congrArg metacicSubstitutionSpineRealizerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetaCICSubstitutionSpineRealizerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetaCICSubstitutionSpineRealizerTasteGate_single_carrier_alignment_round_trip y)))

instance metacicSubstitutionSpineRealizerBHistCarrier :
    BHistCarrier MetaCICSubstitutionSpineRealizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metacicSubstitutionSpineRealizerToEventFlow
  fromEventFlow := metacicSubstitutionSpineRealizerFromEventFlow

instance metacicSubstitutionSpineRealizerChapterTasteGate :
    ChapterTasteGate MetaCICSubstitutionSpineRealizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metacicSubstitutionSpineRealizerFromEventFlow
          (metacicSubstitutionSpineRealizerToEventFlow x) =
        some x
    exact MetaCICSubstitutionSpineRealizerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetaCICSubstitutionSpineRealizerTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem MetaCICSubstitutionSpineRealizerTasteGate_single_carrier_alignment :
    (forall h : BHist,
      metacicSubstitutionSpineRealizerDecodeBHist
          (metacicSubstitutionSpineRealizerEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier MetaCICSubstitutionSpineRealizerUp) ∧
        Nonempty (ChapterTasteGate MetaCICSubstitutionSpineRealizerUp) ∧
          metacicSubstitutionSpineRealizerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨MetaCICSubstitutionSpineRealizerTasteGate_single_carrier_alignment_decode_encode,
      ⟨metacicSubstitutionSpineRealizerBHistCarrier⟩,
      ⟨metacicSubstitutionSpineRealizerChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.MetaCICSubstitutionSpineRealizerUp
