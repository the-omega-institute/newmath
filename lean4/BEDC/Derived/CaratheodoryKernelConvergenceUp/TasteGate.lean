import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CaratheodoryKernelConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CaratheodoryKernelConvergenceUp : Type where
  | mk
      (pointedDomain compactKernel holomorphicChart normalFamily riemannRoute transport
        replay provenance localName : BHist) :
      CaratheodoryKernelConvergenceUp
  deriving DecidableEq

def caratheodoryKernelConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: caratheodoryKernelConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: caratheodoryKernelConvergenceEncodeBHist h

def caratheodoryKernelConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (caratheodoryKernelConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (caratheodoryKernelConvergenceDecodeBHist tail)

private theorem caratheodoryKernelConvergenceDecode_encode_bhist :
    ∀ h : BHist,
      caratheodoryKernelConvergenceDecodeBHist
          (caratheodoryKernelConvergenceEncodeBHist h) =
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

def caratheodoryKernelConvergenceToEventFlow :
    CaratheodoryKernelConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CaratheodoryKernelConvergenceUp.mk pointedDomain compactKernel holomorphicChart
      normalFamily riemannRoute transport replay provenance localName =>
      [[BMark.b0],
        caratheodoryKernelConvergenceEncodeBHist pointedDomain,
        [BMark.b1, BMark.b0],
        caratheodoryKernelConvergenceEncodeBHist compactKernel,
        [BMark.b1, BMark.b1, BMark.b0],
        caratheodoryKernelConvergenceEncodeBHist holomorphicChart,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        caratheodoryKernelConvergenceEncodeBHist normalFamily,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        caratheodoryKernelConvergenceEncodeBHist riemannRoute,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        caratheodoryKernelConvergenceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        caratheodoryKernelConvergenceEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        caratheodoryKernelConvergenceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        caratheodoryKernelConvergenceEncodeBHist localName]

def caratheodoryKernelConvergenceFromEventFlow :
    EventFlow → Option CaratheodoryKernelConvergenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | pointedDomain :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | compactKernel :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | holomorphicChart :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | normalFamily :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | riemannRoute :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | replay :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | localName :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (CaratheodoryKernelConvergenceUp.mk
                                                                                  (caratheodoryKernelConvergenceDecodeBHist pointedDomain)
                                                                                  (caratheodoryKernelConvergenceDecodeBHist compactKernel)
                                                                                  (caratheodoryKernelConvergenceDecodeBHist holomorphicChart)
                                                                                  (caratheodoryKernelConvergenceDecodeBHist normalFamily)
                                                                                  (caratheodoryKernelConvergenceDecodeBHist riemannRoute)
                                                                                  (caratheodoryKernelConvergenceDecodeBHist transport)
                                                                                  (caratheodoryKernelConvergenceDecodeBHist replay)
                                                                                  (caratheodoryKernelConvergenceDecodeBHist provenance)
                                                                                  (caratheodoryKernelConvergenceDecodeBHist localName))
                                                                          | _ :: _ => none

private theorem caratheodoryKernelConvergence_round_trip :
    ∀ x : CaratheodoryKernelConvergenceUp,
      caratheodoryKernelConvergenceFromEventFlow
          (caratheodoryKernelConvergenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk pointedDomain compactKernel holomorphicChart normalFamily riemannRoute transport
      replay provenance localName =>
      change
        some
          (CaratheodoryKernelConvergenceUp.mk
            (caratheodoryKernelConvergenceDecodeBHist
              (caratheodoryKernelConvergenceEncodeBHist pointedDomain))
            (caratheodoryKernelConvergenceDecodeBHist
              (caratheodoryKernelConvergenceEncodeBHist compactKernel))
            (caratheodoryKernelConvergenceDecodeBHist
              (caratheodoryKernelConvergenceEncodeBHist holomorphicChart))
            (caratheodoryKernelConvergenceDecodeBHist
              (caratheodoryKernelConvergenceEncodeBHist normalFamily))
            (caratheodoryKernelConvergenceDecodeBHist
              (caratheodoryKernelConvergenceEncodeBHist riemannRoute))
            (caratheodoryKernelConvergenceDecodeBHist
              (caratheodoryKernelConvergenceEncodeBHist transport))
            (caratheodoryKernelConvergenceDecodeBHist
              (caratheodoryKernelConvergenceEncodeBHist replay))
            (caratheodoryKernelConvergenceDecodeBHist
              (caratheodoryKernelConvergenceEncodeBHist provenance))
            (caratheodoryKernelConvergenceDecodeBHist
              (caratheodoryKernelConvergenceEncodeBHist localName))) =
          some
            (CaratheodoryKernelConvergenceUp.mk pointedDomain compactKernel
              holomorphicChart normalFamily riemannRoute transport replay provenance
              localName)
      rw [caratheodoryKernelConvergenceDecode_encode_bhist pointedDomain,
        caratheodoryKernelConvergenceDecode_encode_bhist compactKernel,
        caratheodoryKernelConvergenceDecode_encode_bhist holomorphicChart,
        caratheodoryKernelConvergenceDecode_encode_bhist normalFamily,
        caratheodoryKernelConvergenceDecode_encode_bhist riemannRoute,
        caratheodoryKernelConvergenceDecode_encode_bhist transport,
        caratheodoryKernelConvergenceDecode_encode_bhist replay,
        caratheodoryKernelConvergenceDecode_encode_bhist provenance,
        caratheodoryKernelConvergenceDecode_encode_bhist localName]

private theorem caratheodoryKernelConvergenceToEventFlow_injective
    {x y : CaratheodoryKernelConvergenceUp} :
    caratheodoryKernelConvergenceToEventFlow x =
        caratheodoryKernelConvergenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      caratheodoryKernelConvergenceFromEventFlow
          (caratheodoryKernelConvergenceToEventFlow x) =
        caratheodoryKernelConvergenceFromEventFlow
          (caratheodoryKernelConvergenceToEventFlow y) :=
    congrArg caratheodoryKernelConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (caratheodoryKernelConvergence_round_trip x).symm
      (Eq.trans hread (caratheodoryKernelConvergence_round_trip y)))

instance caratheodoryKernelConvergenceBHistCarrier :
    BHistCarrier CaratheodoryKernelConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := caratheodoryKernelConvergenceToEventFlow
  fromEventFlow := caratheodoryKernelConvergenceFromEventFlow

instance caratheodoryKernelConvergenceChapterTasteGate :
    ChapterTasteGate CaratheodoryKernelConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      caratheodoryKernelConvergenceFromEventFlow
          (caratheodoryKernelConvergenceToEventFlow x) =
        some x
    exact caratheodoryKernelConvergence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (caratheodoryKernelConvergenceToEventFlow_injective heq)

theorem CaratheodoryKernelConvergenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        caratheodoryKernelConvergenceDecodeBHist
            (caratheodoryKernelConvergenceEncodeBHist h) =
          h) ∧
      Nonempty (BHistCarrier CaratheodoryKernelConvergenceUp) ∧
        Nonempty (ChapterTasteGate CaratheodoryKernelConvergenceUp) ∧
          caratheodoryKernelConvergenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact caratheodoryKernelConvergenceDecode_encode_bhist
  · constructor
    · exact ⟨caratheodoryKernelConvergenceBHistCarrier⟩
    · constructor
      · exact ⟨caratheodoryKernelConvergenceChapterTasteGate⟩
      · rfl

end BEDC.Derived.CaratheodoryKernelConvergenceUp
