import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConvergentNetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConvergentNetUp : Type where
  | mk (D V T L M C H K P N : BHist) : ConvergentNetUp
  deriving DecidableEq

def convergentNetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: convergentNetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: convergentNetEncodeBHist h

def convergentNetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (convergentNetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (convergentNetDecodeBHist tail)

private theorem ConvergentNetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, convergentNetDecodeBHist (convergentNetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def convergentNetToEventFlow : ConvergentNetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ConvergentNetUp.mk D V T L M C H K P N =>
      [convergentNetEncodeBHist D,
        convergentNetEncodeBHist V,
        convergentNetEncodeBHist T,
        convergentNetEncodeBHist L,
        convergentNetEncodeBHist M,
        convergentNetEncodeBHist C,
        convergentNetEncodeBHist H,
        convergentNetEncodeBHist K,
        convergentNetEncodeBHist P,
        convergentNetEncodeBHist N]

def convergentNetFromEventFlow : EventFlow → Option ConvergentNetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | D :: rest0 =>
      match rest0 with
      | [] => none
      | V :: rest1 =>
          match rest1 with
          | [] => none
          | T :: rest2 =>
              match rest2 with
              | [] => none
              | L :: rest3 =>
                  match rest3 with
                  | [] => none
                  | M :: rest4 =>
                      match rest4 with
                      | [] => none
                      | C :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | K :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (ConvergentNetUp.mk
                                                  (convergentNetDecodeBHist D)
                                                  (convergentNetDecodeBHist V)
                                                  (convergentNetDecodeBHist T)
                                                  (convergentNetDecodeBHist L)
                                                  (convergentNetDecodeBHist M)
                                                  (convergentNetDecodeBHist C)
                                                  (convergentNetDecodeBHist H)
                                                  (convergentNetDecodeBHist K)
                                                  (convergentNetDecodeBHist P)
                                                  (convergentNetDecodeBHist N))
                                          | _ :: _ => none

private theorem ConvergentNetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ConvergentNetUp,
      convergentNetFromEventFlow (convergentNetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D V T L M C H K P N =>
      change
        some
          (ConvergentNetUp.mk
            (convergentNetDecodeBHist (convergentNetEncodeBHist D))
            (convergentNetDecodeBHist (convergentNetEncodeBHist V))
            (convergentNetDecodeBHist (convergentNetEncodeBHist T))
            (convergentNetDecodeBHist (convergentNetEncodeBHist L))
            (convergentNetDecodeBHist (convergentNetEncodeBHist M))
            (convergentNetDecodeBHist (convergentNetEncodeBHist C))
            (convergentNetDecodeBHist (convergentNetEncodeBHist H))
            (convergentNetDecodeBHist (convergentNetEncodeBHist K))
            (convergentNetDecodeBHist (convergentNetEncodeBHist P))
            (convergentNetDecodeBHist (convergentNetEncodeBHist N))) =
          some (ConvergentNetUp.mk D V T L M C H K P N)
      rw [ConvergentNetTasteGate_single_carrier_alignment_decode_encode D,
        ConvergentNetTasteGate_single_carrier_alignment_decode_encode V,
        ConvergentNetTasteGate_single_carrier_alignment_decode_encode T,
        ConvergentNetTasteGate_single_carrier_alignment_decode_encode L,
        ConvergentNetTasteGate_single_carrier_alignment_decode_encode M,
        ConvergentNetTasteGate_single_carrier_alignment_decode_encode C,
        ConvergentNetTasteGate_single_carrier_alignment_decode_encode H,
        ConvergentNetTasteGate_single_carrier_alignment_decode_encode K,
        ConvergentNetTasteGate_single_carrier_alignment_decode_encode P,
        ConvergentNetTasteGate_single_carrier_alignment_decode_encode N]

private theorem ConvergentNetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ConvergentNetUp} :
    convergentNetToEventFlow x = convergentNetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      convergentNetFromEventFlow (convergentNetToEventFlow x) =
        convergentNetFromEventFlow (convergentNetToEventFlow y) :=
    congrArg convergentNetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ConvergentNetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ConvergentNetTasteGate_single_carrier_alignment_round_trip y)))

instance convergentNetBHistCarrier : BHistCarrier ConvergentNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := convergentNetToEventFlow
  fromEventFlow := convergentNetFromEventFlow

instance convergentNetChapterTasteGate : ChapterTasteGate ConvergentNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change convergentNetFromEventFlow (convergentNetToEventFlow x) = some x
    exact ConvergentNetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ConvergentNetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate ConvergentNetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  convergentNetChapterTasteGate

theorem ConvergentNetTasteGate_single_carrier_alignment :
    (∀ h : BHist, convergentNetDecodeBHist (convergentNetEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ConvergentNetUp) ∧
        Nonempty (ChapterTasteGate ConvergentNetUp) ∧
          convergentNetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ConvergentNetTasteGate_single_carrier_alignment_decode_encode,
      ⟨convergentNetBHistCarrier⟩,
      ⟨convergentNetChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.ConvergentNetUp
