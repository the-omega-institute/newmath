import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformModulusUp : Type where
  | mk
      (X K F L Q U H C P N : BHist) :
      CompactUniformModulusUp
  deriving DecidableEq

def compactUniformModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformModulusEncodeBHist h

def compactUniformModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformModulusDecodeBHist tail)

private theorem CompactUniformModulusTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, compactUniformModulusDecodeBHist (compactUniformModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactUniformModulusToEventFlow : CompactUniformModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformModulusUp.mk X K F L Q U H C P N =>
      [[BMark.b1, BMark.b1, BMark.b0, BMark.b1],
        compactUniformModulusEncodeBHist X,
        compactUniformModulusEncodeBHist K,
        compactUniformModulusEncodeBHist F,
        compactUniformModulusEncodeBHist L,
        compactUniformModulusEncodeBHist Q,
        compactUniformModulusEncodeBHist U,
        compactUniformModulusEncodeBHist H,
        compactUniformModulusEncodeBHist C,
        compactUniformModulusEncodeBHist P,
        compactUniformModulusEncodeBHist N]

def compactUniformModulusFromEventFlow : EventFlow → Option CompactUniformModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: restX =>
      match restX with
      | [] => none
      | X :: restK =>
          match restK with
          | [] => none
          | K :: restF =>
              match restF with
              | [] => none
              | F :: restL =>
                  match restL with
                  | [] => none
                  | L :: restQ =>
                      match restQ with
                      | [] => none
                      | Q :: restU =>
                          match restU with
                          | [] => none
                          | U :: restH =>
                              match restH with
                              | [] => none
                              | H :: restC =>
                                  match restC with
                                  | [] => none
                                  | C :: restP =>
                                      match restP with
                                      | [] => none
                                      | P :: restN =>
                                          match restN with
                                          | [] => none
                                          | N :: rest =>
                                              match rest with
                                              | [] =>
                                                  some
                                                    (CompactUniformModulusUp.mk
                                                      (compactUniformModulusDecodeBHist X)
                                                      (compactUniformModulusDecodeBHist K)
                                                      (compactUniformModulusDecodeBHist F)
                                                      (compactUniformModulusDecodeBHist L)
                                                      (compactUniformModulusDecodeBHist Q)
                                                      (compactUniformModulusDecodeBHist U)
                                                      (compactUniformModulusDecodeBHist H)
                                                      (compactUniformModulusDecodeBHist C)
                                                      (compactUniformModulusDecodeBHist P)
                                                      (compactUniformModulusDecodeBHist N))
                                              | _ :: _ => none

private theorem CompactUniformModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactUniformModulusUp,
      compactUniformModulusFromEventFlow (compactUniformModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X K F L Q U H C P N =>
      change
        some
          (CompactUniformModulusUp.mk
            (compactUniformModulusDecodeBHist (compactUniformModulusEncodeBHist X))
            (compactUniformModulusDecodeBHist (compactUniformModulusEncodeBHist K))
            (compactUniformModulusDecodeBHist (compactUniformModulusEncodeBHist F))
            (compactUniformModulusDecodeBHist (compactUniformModulusEncodeBHist L))
            (compactUniformModulusDecodeBHist (compactUniformModulusEncodeBHist Q))
            (compactUniformModulusDecodeBHist (compactUniformModulusEncodeBHist U))
            (compactUniformModulusDecodeBHist (compactUniformModulusEncodeBHist H))
            (compactUniformModulusDecodeBHist (compactUniformModulusEncodeBHist C))
            (compactUniformModulusDecodeBHist (compactUniformModulusEncodeBHist P))
            (compactUniformModulusDecodeBHist (compactUniformModulusEncodeBHist N))) =
          some (CompactUniformModulusUp.mk X K F L Q U H C P N)
      rw [CompactUniformModulusTasteGate_single_carrier_alignment_decode_encode X,
        CompactUniformModulusTasteGate_single_carrier_alignment_decode_encode K,
        CompactUniformModulusTasteGate_single_carrier_alignment_decode_encode F,
        CompactUniformModulusTasteGate_single_carrier_alignment_decode_encode L,
        CompactUniformModulusTasteGate_single_carrier_alignment_decode_encode Q,
        CompactUniformModulusTasteGate_single_carrier_alignment_decode_encode U,
        CompactUniformModulusTasteGate_single_carrier_alignment_decode_encode H,
        CompactUniformModulusTasteGate_single_carrier_alignment_decode_encode C,
        CompactUniformModulusTasteGate_single_carrier_alignment_decode_encode P,
        CompactUniformModulusTasteGate_single_carrier_alignment_decode_encode N]

private theorem CompactUniformModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactUniformModulusUp} :
    compactUniformModulusToEventFlow x = compactUniformModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformModulusFromEventFlow (compactUniformModulusToEventFlow x) =
        compactUniformModulusFromEventFlow (compactUniformModulusToEventFlow y) :=
    congrArg compactUniformModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactUniformModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactUniformModulusTasteGate_single_carrier_alignment_round_trip y)))

instance compactUniformModulusBHistCarrier : BHistCarrier CompactUniformModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformModulusToEventFlow
  fromEventFlow := compactUniformModulusFromEventFlow

instance compactUniformModulusChapterTasteGate : ChapterTasteGate CompactUniformModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactUniformModulusFromEventFlow (compactUniformModulusToEventFlow x) = some x
    exact CompactUniformModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompactUniformModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CompactUniformModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist, compactUniformModulusDecodeBHist (compactUniformModulusEncodeBHist h) = h) ∧
      (∀ x : CompactUniformModulusUp,
        compactUniformModulusFromEventFlow (compactUniformModulusToEventFlow x) = some x) ∧
        (∀ x y : CompactUniformModulusUp,
          compactUniformModulusToEventFlow x = compactUniformModulusToEventFlow y → x = y) ∧
          compactUniformModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CompactUniformModulusTasteGate_single_carrier_alignment_decode_encode,
      CompactUniformModulusTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        CompactUniformModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CompactUniformModulusUp
