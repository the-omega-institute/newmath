import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FoldMomentKernelUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FoldMomentKernelUp : Type where
  | mk :
      (window foldSource fiberLedger momentIndex collisionCount transport route provenance
        nameCert : BHist) →
      FoldMomentKernelUp

def foldMomentKernelEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: foldMomentKernelEncodeBHist h
  | BHist.e1 h => BMark.b1 :: foldMomentKernelEncodeBHist h

def foldMomentKernelDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (foldMomentKernelDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (foldMomentKernelDecodeBHist tail)

private theorem foldMomentKernelDecode_encode :
    ∀ h : BHist, foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def foldMomentKernelToEventFlow : FoldMomentKernelUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FoldMomentKernelUp.mk window foldSource fiberLedger momentIndex collisionCount transport
      route provenance nameCert =>
      [[BMark.b0], foldMomentKernelEncodeBHist window,
        [BMark.b1, BMark.b0], foldMomentKernelEncodeBHist foldSource,
        [BMark.b1, BMark.b1, BMark.b0], foldMomentKernelEncodeBHist fiberLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          foldMomentKernelEncodeBHist momentIndex,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          foldMomentKernelEncodeBHist collisionCount,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          foldMomentKernelEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          foldMomentKernelEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
          foldMomentKernelEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
          foldMomentKernelEncodeBHist nameCert]

def foldMomentKernelFromEventFlow : EventFlow → Option FoldMomentKernelUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | window :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | foldSource :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | fiberLedger :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | momentIndex :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | collisionCount :: rest9 =>
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
                                                      | route :: rest13 =>
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
                                                                      | nameCert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (FoldMomentKernelUp.mk
                                                                                  (foldMomentKernelDecodeBHist window)
                                                                                  (foldMomentKernelDecodeBHist foldSource)
                                                                                  (foldMomentKernelDecodeBHist fiberLedger)
                                                                                  (foldMomentKernelDecodeBHist momentIndex)
                                                                                  (foldMomentKernelDecodeBHist collisionCount)
                                                                                  (foldMomentKernelDecodeBHist transport)
                                                                                  (foldMomentKernelDecodeBHist route)
                                                                                  (foldMomentKernelDecodeBHist provenance)
                                                                                  (foldMomentKernelDecodeBHist nameCert))
                                                                          | _ :: _ => none

private theorem foldMomentKernel_round_trip :
    ∀ x : FoldMomentKernelUp,
      foldMomentKernelFromEventFlow (foldMomentKernelToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk window foldSource fiberLedger momentIndex collisionCount transport route provenance
      nameCert =>
      change
        some
          (FoldMomentKernelUp.mk
            (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist window))
            (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist foldSource))
            (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist fiberLedger))
            (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist momentIndex))
            (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist collisionCount))
            (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist transport))
            (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist route))
            (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist provenance))
            (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist nameCert))) =
          some
            (FoldMomentKernelUp.mk window foldSource fiberLedger momentIndex collisionCount
              transport route provenance nameCert)
      rw [foldMomentKernelDecode_encode window, foldMomentKernelDecode_encode foldSource,
        foldMomentKernelDecode_encode fiberLedger, foldMomentKernelDecode_encode momentIndex,
        foldMomentKernelDecode_encode collisionCount, foldMomentKernelDecode_encode transport,
        foldMomentKernelDecode_encode route, foldMomentKernelDecode_encode provenance,
        foldMomentKernelDecode_encode nameCert]

private theorem foldMomentKernelToEventFlow_injective {x y : FoldMomentKernelUp} :
    foldMomentKernelToEventFlow x = foldMomentKernelToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk window foldSource fiberLedger momentIndex collisionCount transport route provenance
      nameCert =>
      cases y with
      | mk window' foldSource' fiberLedger' momentIndex' collisionCount' transport' route'
          provenance' nameCert' =>
          have hread :
              foldMomentKernelFromEventFlow
                  (foldMomentKernelToEventFlow
                    (FoldMomentKernelUp.mk window foldSource fiberLedger momentIndex
                      collisionCount transport route provenance nameCert)) =
                foldMomentKernelFromEventFlow
                  (foldMomentKernelToEventFlow
                    (FoldMomentKernelUp.mk window' foldSource' fiberLedger' momentIndex'
                      collisionCount' transport' route' provenance' nameCert')) :=
            congrArg foldMomentKernelFromEventFlow heq
          exact Option.some.inj
            (Eq.trans
              (foldMomentKernel_round_trip
                (FoldMomentKernelUp.mk window foldSource fiberLedger momentIndex collisionCount
                  transport route provenance nameCert)).symm
              (Eq.trans hread
                (foldMomentKernel_round_trip
                  (FoldMomentKernelUp.mk window' foldSource' fiberLedger' momentIndex'
                    collisionCount' transport' route' provenance' nameCert'))))

instance foldMomentKernelBHistCarrier : BHistCarrier FoldMomentKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := foldMomentKernelToEventFlow
  fromEventFlow := foldMomentKernelFromEventFlow

instance foldMomentKernelChapterTasteGate : ChapterTasteGate FoldMomentKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change foldMomentKernelFromEventFlow (foldMomentKernelToEventFlow x) = some x
    exact foldMomentKernel_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (foldMomentKernelToEventFlow_injective heq)

theorem FoldMomentKernelTasteGate_single_carrier_alignment :
    (forall h : BHist, foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist h) = h) /\
      (forall x : FoldMomentKernelUp,
        foldMomentKernelFromEventFlow (foldMomentKernelToEventFlow x) = some x) /\
      (forall x y : FoldMomentKernelUp,
        foldMomentKernelToEventFlow x = foldMomentKernelToEventFlow y -> x = y) /\
      foldMomentKernelEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  have decodeEncode :
      ∀ h : BHist, foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  have roundTrip :
      ∀ x : FoldMomentKernelUp,
        foldMomentKernelFromEventFlow (foldMomentKernelToEventFlow x) = some x := by
    intro x
    cases x with
    | mk window foldSource fiberLedger momentIndex collisionCount transport route provenance
        nameCert =>
        change
          some
            (FoldMomentKernelUp.mk
              (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist window))
              (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist foldSource))
              (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist fiberLedger))
              (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist momentIndex))
              (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist collisionCount))
              (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist transport))
              (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist route))
              (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist provenance))
              (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist nameCert))) =
            some
              (FoldMomentKernelUp.mk window foldSource fiberLedger momentIndex collisionCount
                transport route provenance nameCert)
        rw [decodeEncode window, decodeEncode foldSource, decodeEncode fiberLedger,
          decodeEncode momentIndex, decodeEncode collisionCount, decodeEncode transport,
          decodeEncode route, decodeEncode provenance, decodeEncode nameCert]
  have injective :
      ∀ x y : FoldMomentKernelUp,
        foldMomentKernelToEventFlow x = foldMomentKernelToEventFlow y → x = y := by
    intro x y heq
    have hread :
        foldMomentKernelFromEventFlow (foldMomentKernelToEventFlow x) =
          foldMomentKernelFromEventFlow (foldMomentKernelToEventFlow y) :=
      congrArg foldMomentKernelFromEventFlow heq
    exact Option.some.inj
      (Eq.trans (roundTrip x).symm (Eq.trans hread (roundTrip y)))
  constructor
  · exact decodeEncode
  · constructor
    · intro x
      exact roundTrip x
    · constructor
      · intro x y heq
        exact injective x y heq
      · rfl

end BEDC.Derived.FoldMomentKernelUp
