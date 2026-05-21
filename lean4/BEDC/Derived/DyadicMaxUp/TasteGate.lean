import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicMaxUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicMaxUp : Type where
  | mk (x y n m L U H C P N : BHist) : DyadicMaxUp
  deriving DecidableEq

def dyadicMaxEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicMaxEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicMaxEncodeBHist h

def dyadicMaxDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicMaxDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicMaxDecodeBHist tail)

private theorem dyadicMax_decode_encode :
    ∀ h : BHist, dyadicMaxDecodeBHist (dyadicMaxEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicMaxFields : DyadicMaxUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicMaxUp.mk x y n m L U H C P N => [x, y, n, m, L, U, H, C, P, N]

def dyadicMaxToEventFlow : DyadicMaxUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token => (dyadicMaxFields token).map dyadicMaxEncodeBHist

def dyadicMaxFromEventFlow : EventFlow → Option DyadicMaxUp
  -- BEDC touchpoint anchor: BHist BMark
  | x :: restX =>
      match restX with
      | y :: restY =>
          match restY with
          | n :: restN =>
              match restN with
              | m :: restM =>
                  match restM with
                  | L :: restL =>
                      match restL with
                      | U :: restU =>
                          match restU with
                          | H :: restH =>
                              match restH with
                              | C :: restC =>
                                  match restC with
                                  | P :: restP =>
                                      match restP with
                                      | N :: restTail =>
                                          match restTail with
                                          | [] =>
                                              some
                                                (DyadicMaxUp.mk
                                                  (dyadicMaxDecodeBHist x)
                                                  (dyadicMaxDecodeBHist y)
                                                  (dyadicMaxDecodeBHist n)
                                                  (dyadicMaxDecodeBHist m)
                                                  (dyadicMaxDecodeBHist L)
                                                  (dyadicMaxDecodeBHist U)
                                                  (dyadicMaxDecodeBHist H)
                                                  (dyadicMaxDecodeBHist C)
                                                  (dyadicMaxDecodeBHist P)
                                                  (dyadicMaxDecodeBHist N))
                                          | _ :: _ => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem dyadicMax_round_trip :
    ∀ token : DyadicMaxUp, dyadicMaxFromEventFlow (dyadicMaxToEventFlow token) = some token := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk x y n m L U H C P N =>
      change
        some
            (DyadicMaxUp.mk
              (dyadicMaxDecodeBHist (dyadicMaxEncodeBHist x))
              (dyadicMaxDecodeBHist (dyadicMaxEncodeBHist y))
              (dyadicMaxDecodeBHist (dyadicMaxEncodeBHist n))
              (dyadicMaxDecodeBHist (dyadicMaxEncodeBHist m))
              (dyadicMaxDecodeBHist (dyadicMaxEncodeBHist L))
              (dyadicMaxDecodeBHist (dyadicMaxEncodeBHist U))
              (dyadicMaxDecodeBHist (dyadicMaxEncodeBHist H))
              (dyadicMaxDecodeBHist (dyadicMaxEncodeBHist C))
              (dyadicMaxDecodeBHist (dyadicMaxEncodeBHist P))
              (dyadicMaxDecodeBHist (dyadicMaxEncodeBHist N))) =
          some (DyadicMaxUp.mk x y n m L U H C P N)
      rw [dyadicMax_decode_encode x]
      rw [dyadicMax_decode_encode y]
      rw [dyadicMax_decode_encode n]
      rw [dyadicMax_decode_encode m]
      rw [dyadicMax_decode_encode L]
      rw [dyadicMax_decode_encode U]
      rw [dyadicMax_decode_encode H]
      rw [dyadicMax_decode_encode C]
      rw [dyadicMax_decode_encode P]
      rw [dyadicMax_decode_encode N]

private theorem dyadicMaxToEventFlow_injective {x y : DyadicMaxUp} :
    dyadicMaxToEventFlow x = dyadicMaxToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicMaxFromEventFlow (dyadicMaxToEventFlow x) =
        dyadicMaxFromEventFlow (dyadicMaxToEventFlow y) :=
    congrArg dyadicMaxFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicMax_round_trip x).symm
      (Eq.trans hread (dyadicMax_round_trip y)))

instance dyadicMaxBHistCarrier : BHistCarrier DyadicMaxUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicMaxToEventFlow
  fromEventFlow := dyadicMaxFromEventFlow

instance dyadicMaxChapterTasteGate : ChapterTasteGate DyadicMaxUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicMaxFromEventFlow (dyadicMaxToEventFlow x) = some x
    exact dyadicMax_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicMaxToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DyadicMaxUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicMaxChapterTasteGate

theorem DyadicMaxTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicMaxDecodeBHist (dyadicMaxEncodeBHist h) = h) ∧
      (∀ x : DyadicMaxUp, dyadicMaxFromEventFlow (dyadicMaxToEventFlow x) = some x) ∧
      (∀ x y : DyadicMaxUp, dyadicMaxToEventFlow x = dyadicMaxToEventFlow y → x = y) ∧
      ∃ x : DyadicMaxUp,
        x =
          DyadicMaxUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty ∧
        dyadicMaxFromEventFlow (dyadicMaxToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact dyadicMax_decode_encode
  constructor
  · intro x
    exact dyadicMax_round_trip x
  constructor
  · intro x y heq
    exact dyadicMaxToEventFlow_injective heq
  · let token :=
      DyadicMaxUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
    exact ⟨token, rfl, dyadicMax_round_trip token⟩

end BEDC.Derived.DyadicMaxUp
