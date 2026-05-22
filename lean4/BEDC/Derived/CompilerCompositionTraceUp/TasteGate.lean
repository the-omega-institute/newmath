import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompilerCompositionTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompilerCompositionTraceUp : Type where
  | mk (S M T KSM KMT J G L H C A P N : BHist) : CompilerCompositionTraceUp
  deriving DecidableEq

def compilerCompositionTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compilerCompositionTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compilerCompositionTraceEncodeBHist h

def compilerCompositionTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compilerCompositionTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compilerCompositionTraceDecodeBHist tail)

private theorem CompilerCompositionTraceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, compilerCompositionTraceDecodeBHist (compilerCompositionTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compilerCompositionTraceFields : CompilerCompositionTraceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompilerCompositionTraceUp.mk S M T KSM KMT J G L H C A P N =>
      [S, M, T, KSM, KMT, J, G, L, H, C, A, P, N]

def compilerCompositionTraceToEventFlow : CompilerCompositionTraceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (compilerCompositionTraceFields x).map compilerCompositionTraceEncodeBHist

private def compilerCompositionTraceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compilerCompositionTraceEventAtDefault index rest

def compilerCompositionTraceFromEventFlow (ef : EventFlow) : Option CompilerCompositionTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompilerCompositionTraceUp.mk
      (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEventAtDefault 0 ef))
      (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEventAtDefault 1 ef))
      (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEventAtDefault 2 ef))
      (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEventAtDefault 3 ef))
      (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEventAtDefault 4 ef))
      (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEventAtDefault 5 ef))
      (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEventAtDefault 6 ef))
      (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEventAtDefault 7 ef))
      (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEventAtDefault 8 ef))
      (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEventAtDefault 9 ef))
      (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEventAtDefault 10 ef))
      (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEventAtDefault 11 ef))
      (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEventAtDefault 12 ef)))

private theorem CompilerCompositionTraceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompilerCompositionTraceUp,
      compilerCompositionTraceFromEventFlow (compilerCompositionTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M T KSM KMT J G L H C A P N =>
      change
        some
            (CompilerCompositionTraceUp.mk
              (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEncodeBHist S))
              (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEncodeBHist M))
              (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEncodeBHist T))
              (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEncodeBHist KSM))
              (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEncodeBHist KMT))
              (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEncodeBHist J))
              (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEncodeBHist G))
              (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEncodeBHist L))
              (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEncodeBHist H))
              (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEncodeBHist C))
              (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEncodeBHist A))
              (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEncodeBHist P))
              (compilerCompositionTraceDecodeBHist (compilerCompositionTraceEncodeBHist N))) =
          some (CompilerCompositionTraceUp.mk S M T KSM KMT J G L H C A P N)
      rw [CompilerCompositionTraceTasteGate_single_carrier_alignment_decode S,
        CompilerCompositionTraceTasteGate_single_carrier_alignment_decode M,
        CompilerCompositionTraceTasteGate_single_carrier_alignment_decode T,
        CompilerCompositionTraceTasteGate_single_carrier_alignment_decode KSM,
        CompilerCompositionTraceTasteGate_single_carrier_alignment_decode KMT,
        CompilerCompositionTraceTasteGate_single_carrier_alignment_decode J,
        CompilerCompositionTraceTasteGate_single_carrier_alignment_decode G,
        CompilerCompositionTraceTasteGate_single_carrier_alignment_decode L,
        CompilerCompositionTraceTasteGate_single_carrier_alignment_decode H,
        CompilerCompositionTraceTasteGate_single_carrier_alignment_decode C,
        CompilerCompositionTraceTasteGate_single_carrier_alignment_decode A,
        CompilerCompositionTraceTasteGate_single_carrier_alignment_decode P,
        CompilerCompositionTraceTasteGate_single_carrier_alignment_decode N]

private theorem CompilerCompositionTraceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompilerCompositionTraceUp} :
    compilerCompositionTraceToEventFlow x = compilerCompositionTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compilerCompositionTraceFromEventFlow (compilerCompositionTraceToEventFlow x) =
        compilerCompositionTraceFromEventFlow (compilerCompositionTraceToEventFlow y) :=
    congrArg compilerCompositionTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompilerCompositionTraceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CompilerCompositionTraceTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompilerCompositionTraceTasteGate_single_carrier_alignment_fields :
    ∀ x y : CompilerCompositionTraceUp,
      compilerCompositionTraceFields x = compilerCompositionTraceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 M1 T1 KSM1 KMT1 J1 G1 L1 H1 C1 A1 P1 N1 =>
      cases y with
      | mk S2 M2 T2 KSM2 KMT2 J2 G2 L2 H2 C2 A2 P2 N2 =>
          cases hfields
          rfl

instance compilerCompositionTraceBHistCarrier : BHistCarrier CompilerCompositionTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compilerCompositionTraceToEventFlow
  fromEventFlow := compilerCompositionTraceFromEventFlow

instance compilerCompositionTraceChapterTasteGate :
    ChapterTasteGate CompilerCompositionTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compilerCompositionTraceFromEventFlow (compilerCompositionTraceToEventFlow x) = some x
    exact CompilerCompositionTraceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompilerCompositionTraceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance compilerCompositionTraceFieldFaithful : FieldFaithful CompilerCompositionTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compilerCompositionTraceFields
  field_faithful := CompilerCompositionTraceTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate CompilerCompositionTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compilerCompositionTraceChapterTasteGate

theorem CompilerCompositionTraceTasteGate_single_carrier_alignment :
    (∀ h : BHist, compilerCompositionTraceDecodeBHist (compilerCompositionTraceEncodeBHist h) = h) ∧
      (∀ x : CompilerCompositionTraceUp,
        compilerCompositionTraceFromEventFlow (compilerCompositionTraceToEventFlow x) = some x) ∧
        (∀ x y : CompilerCompositionTraceUp,
          compilerCompositionTraceToEventFlow x = compilerCompositionTraceToEventFlow y → x = y) ∧
          compilerCompositionTraceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨CompilerCompositionTraceTasteGate_single_carrier_alignment_decode,
      CompilerCompositionTraceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CompilerCompositionTraceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompilerCompositionTraceUp
