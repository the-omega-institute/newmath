import BEDC.Derived.RegularCauchyLimitModulusUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyLimitModulusUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyLimitModulusUp : Type where
  | mk :
      (input modulus precision threshold window readback dyadicLedger sealRow provenance cert :
        BHist) →
        RegularCauchyLimitModulusUp
  deriving DecidableEq

def RegularCauchyLimitModulusTasteGate_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0, BMark.b1, BMark.b1, BMark.b0]

def RegularCauchyLimitModulusTasteGate_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: RegularCauchyLimitModulusTasteGate_encodeBHist h
  | BHist.e1 h => BMark.b1 :: RegularCauchyLimitModulusTasteGate_encodeBHist h

def RegularCauchyLimitModulusTasteGate_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (RegularCauchyLimitModulusTasteGate_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (RegularCauchyLimitModulusTasteGate_decodeBHist tail)

private theorem RegularCauchyLimitModulusTasteGate_decode_encode :
    ∀ h : BHist,
      RegularCauchyLimitModulusTasteGate_decodeBHist
          (RegularCauchyLimitModulusTasteGate_encodeBHist h) =
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

def RegularCauchyLimitModulusTasteGate_toEventFlow :
    RegularCauchyLimitModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyLimitModulusUp.mk input modulus precision threshold window readback
      dyadicLedger sealRow provenance cert =>
      [RegularCauchyLimitModulusTasteGate_tag,
        RegularCauchyLimitModulusTasteGate_encodeBHist input,
        RegularCauchyLimitModulusTasteGate_encodeBHist modulus,
        RegularCauchyLimitModulusTasteGate_encodeBHist precision,
        RegularCauchyLimitModulusTasteGate_encodeBHist threshold,
        RegularCauchyLimitModulusTasteGate_encodeBHist window,
        RegularCauchyLimitModulusTasteGate_encodeBHist readback,
        RegularCauchyLimitModulusTasteGate_encodeBHist dyadicLedger,
        RegularCauchyLimitModulusTasteGate_encodeBHist sealRow,
        RegularCauchyLimitModulusTasteGate_encodeBHist provenance,
        RegularCauchyLimitModulusTasteGate_encodeBHist cert]

def RegularCauchyLimitModulusTasteGate_fromEventFlow :
    EventFlow → Option RegularCauchyLimitModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [tag, input, modulus, precision, threshold, window, readback, dyadicLedger,
      sealRow, provenance, cert] =>
      match tag with
      | [BMark.b1, BMark.b0, BMark.b1, BMark.b1, BMark.b0] =>
          some
            (RegularCauchyLimitModulusUp.mk
              (RegularCauchyLimitModulusTasteGate_decodeBHist input)
              (RegularCauchyLimitModulusTasteGate_decodeBHist modulus)
              (RegularCauchyLimitModulusTasteGate_decodeBHist precision)
              (RegularCauchyLimitModulusTasteGate_decodeBHist threshold)
              (RegularCauchyLimitModulusTasteGate_decodeBHist window)
              (RegularCauchyLimitModulusTasteGate_decodeBHist readback)
              (RegularCauchyLimitModulusTasteGate_decodeBHist dyadicLedger)
              (RegularCauchyLimitModulusTasteGate_decodeBHist sealRow)
              (RegularCauchyLimitModulusTasteGate_decodeBHist provenance)
              (RegularCauchyLimitModulusTasteGate_decodeBHist cert))
      | _ => none
  | _ => none

private theorem RegularCauchyLimitModulusTasteGate_round_trip :
    ∀ x : RegularCauchyLimitModulusUp,
      RegularCauchyLimitModulusTasteGate_fromEventFlow
          (RegularCauchyLimitModulusTasteGate_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk input modulus precision threshold window readback dyadicLedger sealRow provenance cert =>
      change
        some
          (RegularCauchyLimitModulusUp.mk
            (RegularCauchyLimitModulusTasteGate_decodeBHist
              (RegularCauchyLimitModulusTasteGate_encodeBHist input))
            (RegularCauchyLimitModulusTasteGate_decodeBHist
              (RegularCauchyLimitModulusTasteGate_encodeBHist modulus))
            (RegularCauchyLimitModulusTasteGate_decodeBHist
              (RegularCauchyLimitModulusTasteGate_encodeBHist precision))
            (RegularCauchyLimitModulusTasteGate_decodeBHist
              (RegularCauchyLimitModulusTasteGate_encodeBHist threshold))
            (RegularCauchyLimitModulusTasteGate_decodeBHist
              (RegularCauchyLimitModulusTasteGate_encodeBHist window))
            (RegularCauchyLimitModulusTasteGate_decodeBHist
              (RegularCauchyLimitModulusTasteGate_encodeBHist readback))
            (RegularCauchyLimitModulusTasteGate_decodeBHist
              (RegularCauchyLimitModulusTasteGate_encodeBHist dyadicLedger))
            (RegularCauchyLimitModulusTasteGate_decodeBHist
              (RegularCauchyLimitModulusTasteGate_encodeBHist sealRow))
            (RegularCauchyLimitModulusTasteGate_decodeBHist
              (RegularCauchyLimitModulusTasteGate_encodeBHist provenance))
            (RegularCauchyLimitModulusTasteGate_decodeBHist
              (RegularCauchyLimitModulusTasteGate_encodeBHist cert))) =
          some
            (RegularCauchyLimitModulusUp.mk input modulus precision threshold window readback
              dyadicLedger sealRow provenance cert)
      rw [RegularCauchyLimitModulusTasteGate_decode_encode input,
        RegularCauchyLimitModulusTasteGate_decode_encode modulus,
        RegularCauchyLimitModulusTasteGate_decode_encode precision,
        RegularCauchyLimitModulusTasteGate_decode_encode threshold,
        RegularCauchyLimitModulusTasteGate_decode_encode window,
        RegularCauchyLimitModulusTasteGate_decode_encode readback,
        RegularCauchyLimitModulusTasteGate_decode_encode dyadicLedger,
        RegularCauchyLimitModulusTasteGate_decode_encode sealRow,
        RegularCauchyLimitModulusTasteGate_decode_encode provenance,
        RegularCauchyLimitModulusTasteGate_decode_encode cert]

private theorem RegularCauchyLimitModulusTasteGate_toEventFlow_injective
    {x y : RegularCauchyLimitModulusUp} :
    RegularCauchyLimitModulusTasteGate_toEventFlow x =
        RegularCauchyLimitModulusTasteGate_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      RegularCauchyLimitModulusTasteGate_fromEventFlow
          (RegularCauchyLimitModulusTasteGate_toEventFlow x) =
        RegularCauchyLimitModulusTasteGate_fromEventFlow
          (RegularCauchyLimitModulusTasteGate_toEventFlow y) :=
    congrArg RegularCauchyLimitModulusTasteGate_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchyLimitModulusTasteGate_round_trip x).symm
      (Eq.trans hread (RegularCauchyLimitModulusTasteGate_round_trip y)))

instance RegularCauchyLimitModulusBHistCarrier :
    BHistCarrier RegularCauchyLimitModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RegularCauchyLimitModulusTasteGate_toEventFlow
  fromEventFlow := RegularCauchyLimitModulusTasteGate_fromEventFlow

instance RegularCauchyLimitModulusChapterTasteGate :
    ChapterTasteGate RegularCauchyLimitModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      RegularCauchyLimitModulusTasteGate_fromEventFlow
          (RegularCauchyLimitModulusTasteGate_toEventFlow x) =
        some x
    exact RegularCauchyLimitModulusTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyLimitModulusTasteGate_toEventFlow_injective heq)

def RegularCauchyLimitModulusClassifier :
    RegularCauchyLimitModulusUp → RegularCauchyLimitModulusUp → Prop
  -- BEDC touchpoint anchor: BHist hsame Cont
  | RegularCauchyLimitModulusUp.mk input modulus precision threshold window readback
      dyadicLedger sealRow provenance cert,
    RegularCauchyLimitModulusUp.mk input' modulus' precision' threshold' window' readback'
      dyadicLedger' sealRow' provenance' cert' =>
      hsame input input' ∧ hsame modulus modulus' ∧ hsame precision precision' ∧
        hsame threshold threshold' ∧ hsame window window' ∧ hsame readback readback' ∧
          hsame dyadicLedger dyadicLedger' ∧ hsame sealRow sealRow' ∧
            hsame provenance provenance' ∧ hsame cert cert' ∧
              Cont input modulus threshold ∧ Cont threshold precision window ∧
                Cont window readback dyadicLedger ∧ Cont dyadicLedger sealRow cert ∧
                  Cont input' modulus' threshold' ∧ Cont threshold' precision' window' ∧
                    Cont window' readback' dyadicLedger' ∧
                      Cont dyadicLedger' sealRow' cert'

end BEDC.Derived.RegularCauchyLimitModulusUp
