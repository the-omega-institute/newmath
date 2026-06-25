import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EmptyBoundarySelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EmptyBoundarySelectorUp : Type where
  | mk (H M R E W T C P N : BHist) : EmptyBoundarySelectorUp
  deriving DecidableEq

def emptyBoundarySelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: emptyBoundarySelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: emptyBoundarySelectorEncodeBHist h

def emptyBoundarySelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (emptyBoundarySelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (emptyBoundarySelectorDecodeBHist tail)

theorem EmptyBoundarySelectorTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      emptyBoundarySelectorDecodeBHist (emptyBoundarySelectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def emptyBoundarySelectorToEventFlow : EmptyBoundarySelectorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | EmptyBoundarySelectorUp.mk H M R E W T C P N =>
      [emptyBoundarySelectorEncodeBHist H, emptyBoundarySelectorEncodeBHist M,
        emptyBoundarySelectorEncodeBHist R, emptyBoundarySelectorEncodeBHist E,
        emptyBoundarySelectorEncodeBHist W, emptyBoundarySelectorEncodeBHist T,
        emptyBoundarySelectorEncodeBHist C, emptyBoundarySelectorEncodeBHist P,
        emptyBoundarySelectorEncodeBHist N]

def emptyBoundarySelectorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => emptyBoundarySelectorEventAtDefault index rest

def emptyBoundarySelectorFromEventFlow (ef : EventFlow) :
    Option EmptyBoundarySelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EmptyBoundarySelectorUp.mk
      (emptyBoundarySelectorDecodeBHist (emptyBoundarySelectorEventAtDefault 0 ef))
      (emptyBoundarySelectorDecodeBHist (emptyBoundarySelectorEventAtDefault 1 ef))
      (emptyBoundarySelectorDecodeBHist (emptyBoundarySelectorEventAtDefault 2 ef))
      (emptyBoundarySelectorDecodeBHist (emptyBoundarySelectorEventAtDefault 3 ef))
      (emptyBoundarySelectorDecodeBHist (emptyBoundarySelectorEventAtDefault 4 ef))
      (emptyBoundarySelectorDecodeBHist (emptyBoundarySelectorEventAtDefault 5 ef))
      (emptyBoundarySelectorDecodeBHist (emptyBoundarySelectorEventAtDefault 6 ef))
      (emptyBoundarySelectorDecodeBHist (emptyBoundarySelectorEventAtDefault 7 ef))
      (emptyBoundarySelectorDecodeBHist (emptyBoundarySelectorEventAtDefault 8 ef)))

theorem EmptyBoundarySelectorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : EmptyBoundarySelectorUp,
      emptyBoundarySelectorFromEventFlow (emptyBoundarySelectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk H M R E W T C P N =>
      change
        some
          (EmptyBoundarySelectorUp.mk
            (emptyBoundarySelectorDecodeBHist (emptyBoundarySelectorEncodeBHist H))
            (emptyBoundarySelectorDecodeBHist (emptyBoundarySelectorEncodeBHist M))
            (emptyBoundarySelectorDecodeBHist (emptyBoundarySelectorEncodeBHist R))
            (emptyBoundarySelectorDecodeBHist (emptyBoundarySelectorEncodeBHist E))
            (emptyBoundarySelectorDecodeBHist (emptyBoundarySelectorEncodeBHist W))
            (emptyBoundarySelectorDecodeBHist (emptyBoundarySelectorEncodeBHist T))
            (emptyBoundarySelectorDecodeBHist (emptyBoundarySelectorEncodeBHist C))
            (emptyBoundarySelectorDecodeBHist (emptyBoundarySelectorEncodeBHist P))
            (emptyBoundarySelectorDecodeBHist (emptyBoundarySelectorEncodeBHist N))) =
          some (EmptyBoundarySelectorUp.mk H M R E W T C P N)
      rw [EmptyBoundarySelectorTasteGate_single_carrier_alignment_decode_encode H,
        EmptyBoundarySelectorTasteGate_single_carrier_alignment_decode_encode M,
        EmptyBoundarySelectorTasteGate_single_carrier_alignment_decode_encode R,
        EmptyBoundarySelectorTasteGate_single_carrier_alignment_decode_encode E,
        EmptyBoundarySelectorTasteGate_single_carrier_alignment_decode_encode W,
        EmptyBoundarySelectorTasteGate_single_carrier_alignment_decode_encode T,
        EmptyBoundarySelectorTasteGate_single_carrier_alignment_decode_encode C,
        EmptyBoundarySelectorTasteGate_single_carrier_alignment_decode_encode P,
        EmptyBoundarySelectorTasteGate_single_carrier_alignment_decode_encode N]

theorem EmptyBoundarySelectorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : EmptyBoundarySelectorUp} :
    emptyBoundarySelectorToEventFlow x = emptyBoundarySelectorToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hread :
      emptyBoundarySelectorFromEventFlow (emptyBoundarySelectorToEventFlow x) =
        emptyBoundarySelectorFromEventFlow (emptyBoundarySelectorToEventFlow y) :=
    congrArg emptyBoundarySelectorFromEventFlow hxy
  exact Option.some.inj
    (Eq.trans (EmptyBoundarySelectorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (EmptyBoundarySelectorTasteGate_single_carrier_alignment_round_trip y)))

instance emptyBoundarySelectorBHistCarrier :
    BHistCarrier EmptyBoundarySelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := emptyBoundarySelectorToEventFlow
  fromEventFlow := emptyBoundarySelectorFromEventFlow

instance emptyBoundarySelectorChapterTasteGate :
    ChapterTasteGate EmptyBoundarySelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change emptyBoundarySelectorFromEventFlow (emptyBoundarySelectorToEventFlow x) = some x
    exact EmptyBoundarySelectorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (EmptyBoundarySelectorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem EmptyBoundarySelectorTasteGate_single_carrier_alignment :
    (∀ h : BHist, emptyBoundarySelectorDecodeBHist (emptyBoundarySelectorEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier EmptyBoundarySelectorUp) ∧
        Nonempty (ChapterTasteGate EmptyBoundarySelectorUp) ∧
          emptyBoundarySelectorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨EmptyBoundarySelectorTasteGate_single_carrier_alignment_decode_encode,
      Nonempty.intro emptyBoundarySelectorBHistCarrier,
      Nonempty.intro emptyBoundarySelectorChapterTasteGate,
      rfl⟩

theorem EmptyBoundarySelectorWitness_exposure
    {H M R E W T C P N boundaryRead witnessRead nameRead : BHist} :
    UnaryHistory E →
      UnaryHistory W →
        UnaryHistory T →
          UnaryHistory N →
            Cont E W boundaryRead →
              Cont boundaryRead T witnessRead →
                Cont witnessRead N nameRead →
                  emptyBoundarySelectorFromEventFlow
                      (emptyBoundarySelectorToEventFlow
                        (EmptyBoundarySelectorUp.mk H M R E W T C P N)) =
                    some (EmptyBoundarySelectorUp.mk H M R E W T C P N) →
                    UnaryHistory boundaryRead ∧
                      UnaryHistory witnessRead ∧
                        UnaryHistory nameRead ∧
                          hsame
                            (emptyBoundarySelectorDecodeBHist
                              (emptyBoundarySelectorEncodeBHist W))
                            W := by
  -- BEDC touchpoint anchor: BHist hsame Cont ChapterTasteGate
  intro eUnary wUnary tUnary nUnary boundaryRoute witnessRoute nameRoute _readback
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed eUnary wUnary boundaryRoute
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed boundaryUnary tUnary witnessRoute
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed witnessUnary nUnary nameRoute
  exact
    ⟨boundaryUnary,
      witnessUnary,
      nameUnary,
      EmptyBoundarySelectorTasteGate_single_carrier_alignment_decode_encode W⟩

end BEDC.Derived.EmptyBoundarySelectorUp
