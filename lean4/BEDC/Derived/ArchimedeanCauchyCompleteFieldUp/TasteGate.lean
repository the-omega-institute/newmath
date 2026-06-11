import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArchimedeanCauchyCompleteFieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArchimedeanCauchyCompleteFieldUp : Type where
  | mk (R Q D S O K F H C P N : BHist) : ArchimedeanCauchyCompleteFieldUp
  deriving DecidableEq

def archimedeanCauchyCompleteFieldEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: archimedeanCauchyCompleteFieldEncodeBHist h
  | BHist.e1 h => BMark.b1 :: archimedeanCauchyCompleteFieldEncodeBHist h

def archimedeanCauchyCompleteFieldDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (archimedeanCauchyCompleteFieldDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (archimedeanCauchyCompleteFieldDecodeBHist tail)

private theorem ArchimedeanCauchyCompleteFieldTasteGate_decode :
    ∀ h : BHist,
      archimedeanCauchyCompleteFieldDecodeBHist
        (archimedeanCauchyCompleteFieldEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def archimedeanCauchyCompleteFieldToEventFlow :
    ArchimedeanCauchyCompleteFieldUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ArchimedeanCauchyCompleteFieldUp.mk R Q D S O K F H C P N =>
      [archimedeanCauchyCompleteFieldEncodeBHist R,
        archimedeanCauchyCompleteFieldEncodeBHist Q,
        archimedeanCauchyCompleteFieldEncodeBHist D,
        archimedeanCauchyCompleteFieldEncodeBHist S,
        archimedeanCauchyCompleteFieldEncodeBHist O,
        archimedeanCauchyCompleteFieldEncodeBHist K,
        archimedeanCauchyCompleteFieldEncodeBHist F,
        archimedeanCauchyCompleteFieldEncodeBHist H,
        archimedeanCauchyCompleteFieldEncodeBHist C,
        archimedeanCauchyCompleteFieldEncodeBHist P,
        archimedeanCauchyCompleteFieldEncodeBHist N]

def archimedeanCauchyCompleteFieldFromEventFlow :
    EventFlow → Option ArchimedeanCauchyCompleteFieldUp
  -- BEDC touchpoint anchor: BHist BMark
  | R :: Q :: D :: S :: O :: K :: F :: H :: C :: P :: N :: [] =>
      some
        (ArchimedeanCauchyCompleteFieldUp.mk
          (archimedeanCauchyCompleteFieldDecodeBHist R)
          (archimedeanCauchyCompleteFieldDecodeBHist Q)
          (archimedeanCauchyCompleteFieldDecodeBHist D)
          (archimedeanCauchyCompleteFieldDecodeBHist S)
          (archimedeanCauchyCompleteFieldDecodeBHist O)
          (archimedeanCauchyCompleteFieldDecodeBHist K)
          (archimedeanCauchyCompleteFieldDecodeBHist F)
          (archimedeanCauchyCompleteFieldDecodeBHist H)
          (archimedeanCauchyCompleteFieldDecodeBHist C)
          (archimedeanCauchyCompleteFieldDecodeBHist P)
          (archimedeanCauchyCompleteFieldDecodeBHist N))
  | _ => none

private theorem ArchimedeanCauchyCompleteFieldTasteGate_round_trip :
    ∀ x : ArchimedeanCauchyCompleteFieldUp,
      archimedeanCauchyCompleteFieldFromEventFlow
        (archimedeanCauchyCompleteFieldToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R Q D S O K F H C P N =>
      change
        some
          (ArchimedeanCauchyCompleteFieldUp.mk
            (archimedeanCauchyCompleteFieldDecodeBHist
              (archimedeanCauchyCompleteFieldEncodeBHist R))
            (archimedeanCauchyCompleteFieldDecodeBHist
              (archimedeanCauchyCompleteFieldEncodeBHist Q))
            (archimedeanCauchyCompleteFieldDecodeBHist
              (archimedeanCauchyCompleteFieldEncodeBHist D))
            (archimedeanCauchyCompleteFieldDecodeBHist
              (archimedeanCauchyCompleteFieldEncodeBHist S))
            (archimedeanCauchyCompleteFieldDecodeBHist
              (archimedeanCauchyCompleteFieldEncodeBHist O))
            (archimedeanCauchyCompleteFieldDecodeBHist
              (archimedeanCauchyCompleteFieldEncodeBHist K))
            (archimedeanCauchyCompleteFieldDecodeBHist
              (archimedeanCauchyCompleteFieldEncodeBHist F))
            (archimedeanCauchyCompleteFieldDecodeBHist
              (archimedeanCauchyCompleteFieldEncodeBHist H))
            (archimedeanCauchyCompleteFieldDecodeBHist
              (archimedeanCauchyCompleteFieldEncodeBHist C))
            (archimedeanCauchyCompleteFieldDecodeBHist
              (archimedeanCauchyCompleteFieldEncodeBHist P))
            (archimedeanCauchyCompleteFieldDecodeBHist
              (archimedeanCauchyCompleteFieldEncodeBHist N))) =
          some (ArchimedeanCauchyCompleteFieldUp.mk R Q D S O K F H C P N)
      rw [ArchimedeanCauchyCompleteFieldTasteGate_decode R,
        ArchimedeanCauchyCompleteFieldTasteGate_decode Q,
        ArchimedeanCauchyCompleteFieldTasteGate_decode D,
        ArchimedeanCauchyCompleteFieldTasteGate_decode S,
        ArchimedeanCauchyCompleteFieldTasteGate_decode O,
        ArchimedeanCauchyCompleteFieldTasteGate_decode K,
        ArchimedeanCauchyCompleteFieldTasteGate_decode F,
        ArchimedeanCauchyCompleteFieldTasteGate_decode H,
        ArchimedeanCauchyCompleteFieldTasteGate_decode C,
        ArchimedeanCauchyCompleteFieldTasteGate_decode P,
        ArchimedeanCauchyCompleteFieldTasteGate_decode N]

private theorem ArchimedeanCauchyCompleteFieldToEventFlow_injective
    {x y : ArchimedeanCauchyCompleteFieldUp} :
    archimedeanCauchyCompleteFieldToEventFlow x =
      archimedeanCauchyCompleteFieldToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      archimedeanCauchyCompleteFieldFromEventFlow
          (archimedeanCauchyCompleteFieldToEventFlow x) =
        archimedeanCauchyCompleteFieldFromEventFlow
          (archimedeanCauchyCompleteFieldToEventFlow y) :=
    congrArg archimedeanCauchyCompleteFieldFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ArchimedeanCauchyCompleteFieldTasteGate_round_trip x).symm
      (Eq.trans hread (ArchimedeanCauchyCompleteFieldTasteGate_round_trip y)))

def archimedeanCauchyCompleteFieldBHistCarrierData :
    BHistCarrier ArchimedeanCauchyCompleteFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := archimedeanCauchyCompleteFieldToEventFlow
  fromEventFlow := archimedeanCauchyCompleteFieldFromEventFlow

instance archimedeanCauchyCompleteFieldBHistCarrier :
    BHistCarrier ArchimedeanCauchyCompleteFieldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  archimedeanCauchyCompleteFieldBHistCarrierData

def archimedeanCauchyCompleteFieldChapterTasteGateData :
    @ChapterTasteGate ArchimedeanCauchyCompleteFieldUp
      archimedeanCauchyCompleteFieldBHistCarrierData where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      archimedeanCauchyCompleteFieldFromEventFlow
        (archimedeanCauchyCompleteFieldToEventFlow x) = some x
    exact ArchimedeanCauchyCompleteFieldTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ArchimedeanCauchyCompleteFieldToEventFlow_injective heq)

instance archimedeanCauchyCompleteFieldChapterTasteGate :
    ChapterTasteGate ArchimedeanCauchyCompleteFieldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  archimedeanCauchyCompleteFieldChapterTasteGateData

end BEDC.Derived.ArchimedeanCauchyCompleteFieldUp
