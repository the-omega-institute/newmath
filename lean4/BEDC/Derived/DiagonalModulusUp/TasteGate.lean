import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiagonalModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiagonalModulusUp : Type where
  | mk
      (precision threshold window readback ledger sealRow provenance nameCert : BHist) :
      DiagonalModulusUp
  deriving DecidableEq

def diagonalModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diagonalModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diagonalModulusEncodeBHist h

def diagonalModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diagonalModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diagonalModulusDecodeBHist tail)

private theorem DiagonalModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, diagonalModulusDecodeBHist (diagonalModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def diagonalModulusToEventFlow : DiagonalModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DiagonalModulusUp.mk precision threshold window readback ledger sealRow provenance nameCert =>
      [[BMark.b0],
        diagonalModulusEncodeBHist precision,
        [BMark.b1, BMark.b0],
        diagonalModulusEncodeBHist threshold,
        [BMark.b1, BMark.b1, BMark.b0],
        diagonalModulusEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalModulusEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalModulusEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalModulusEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalModulusEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        diagonalModulusEncodeBHist nameCert]

def diagonalModulusFromEventFlow : EventFlow → Option DiagonalModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tagPrecision :: restPrecision =>
      match restPrecision with
      | [] => none
      | precision :: restThresholdTag =>
          match restThresholdTag with
          | [] => none
          | _tagThreshold :: restThreshold =>
              match restThreshold with
              | [] => none
              | threshold :: restWindowTag =>
                  match restWindowTag with
                  | [] => none
                  | _tagWindow :: restWindow =>
                      match restWindow with
                      | [] => none
                      | window :: restReadbackTag =>
                          match restReadbackTag with
                          | [] => none
                          | _tagReadback :: restReadback =>
                              match restReadback with
                              | [] => none
                              | readback :: restLedgerTag =>
                                  match restLedgerTag with
                                  | [] => none
                                  | _tagLedger :: restLedger =>
                                      match restLedger with
                                      | [] => none
                                      | ledger :: restSealTag =>
                                          match restSealTag with
                                          | [] => none
                                          | _tagSeal :: restSeal =>
                                              match restSeal with
                                              | [] => none
                                              | sealRow :: restProvenanceTag =>
                                                  match restProvenanceTag with
                                                  | [] => none
                                                  | _tagProvenance :: restProvenance =>
                                                      match restProvenance with
                                                      | [] => none
                                                      | provenance :: restNameCertTag =>
                                                          match restNameCertTag with
                                                          | [] => none
                                                          | _tagNameCert :: restNameCert =>
                                                              match restNameCert with
                                                              | [] => none
                                                              | nameCert :: rest =>
                                                                  match rest with
                                                                  | [] =>
                                                                      some
                                                                        (DiagonalModulusUp.mk
                                                                          (diagonalModulusDecodeBHist
                                                                            precision)
                                                                          (diagonalModulusDecodeBHist
                                                                            threshold)
                                                                          (diagonalModulusDecodeBHist
                                                                            window)
                                                                          (diagonalModulusDecodeBHist
                                                                            readback)
                                                                          (diagonalModulusDecodeBHist
                                                                            ledger)
                                                                          (diagonalModulusDecodeBHist
                                                                            sealRow)
                                                                          (diagonalModulusDecodeBHist
                                                                            provenance)
                                                                          (diagonalModulusDecodeBHist
                                                                            nameCert))
                                                                  | _ :: _ => none

private theorem DiagonalModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DiagonalModulusUp,
      diagonalModulusFromEventFlow (diagonalModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk precision threshold window readback ledger sealRow provenance nameCert =>
      change
        some
          (DiagonalModulusUp.mk
            (diagonalModulusDecodeBHist (diagonalModulusEncodeBHist precision))
            (diagonalModulusDecodeBHist (diagonalModulusEncodeBHist threshold))
            (diagonalModulusDecodeBHist (diagonalModulusEncodeBHist window))
            (diagonalModulusDecodeBHist (diagonalModulusEncodeBHist readback))
            (diagonalModulusDecodeBHist (diagonalModulusEncodeBHist ledger))
            (diagonalModulusDecodeBHist (diagonalModulusEncodeBHist sealRow))
            (diagonalModulusDecodeBHist (diagonalModulusEncodeBHist provenance))
            (diagonalModulusDecodeBHist (diagonalModulusEncodeBHist nameCert))) =
          some
            (DiagonalModulusUp.mk precision threshold window readback ledger sealRow provenance
              nameCert)
      rw [DiagonalModulusTasteGate_single_carrier_alignment_decode precision,
        DiagonalModulusTasteGate_single_carrier_alignment_decode threshold,
        DiagonalModulusTasteGate_single_carrier_alignment_decode window,
        DiagonalModulusTasteGate_single_carrier_alignment_decode readback,
        DiagonalModulusTasteGate_single_carrier_alignment_decode ledger,
        DiagonalModulusTasteGate_single_carrier_alignment_decode sealRow,
        DiagonalModulusTasteGate_single_carrier_alignment_decode provenance,
        DiagonalModulusTasteGate_single_carrier_alignment_decode nameCert]

private theorem DiagonalModulusTasteGate_single_carrier_alignment_injective
    {x y : DiagonalModulusUp} :
    diagonalModulusToEventFlow x = diagonalModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      diagonalModulusFromEventFlow (diagonalModulusToEventFlow x) =
        diagonalModulusFromEventFlow (diagonalModulusToEventFlow y) :=
    congrArg diagonalModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DiagonalModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DiagonalModulusTasteGate_single_carrier_alignment_round_trip y)))

instance diagonalModulusBHistCarrier : BHistCarrier DiagonalModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := diagonalModulusToEventFlow
  fromEventFlow := diagonalModulusFromEventFlow

instance diagonalModulusChapterTasteGate : ChapterTasteGate DiagonalModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change diagonalModulusFromEventFlow (diagonalModulusToEventFlow x) = some x
    exact DiagonalModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DiagonalModulusTasteGate_single_carrier_alignment_injective heq)

theorem DiagonalModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist, diagonalModulusDecodeBHist (diagonalModulusEncodeBHist h) = h) ∧
      (∀ x : DiagonalModulusUp,
        diagonalModulusFromEventFlow (diagonalModulusToEventFlow x) = some x) ∧
        (∀ x y : DiagonalModulusUp,
          diagonalModulusToEventFlow x = diagonalModulusToEventFlow y → x = y) ∧
          diagonalModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · intro x
    cases x with
    | mk precision threshold window readback ledger sealRow provenance nameCert =>
        change
          some
            (DiagonalModulusUp.mk
              (diagonalModulusDecodeBHist (diagonalModulusEncodeBHist precision))
              (diagonalModulusDecodeBHist (diagonalModulusEncodeBHist threshold))
              (diagonalModulusDecodeBHist (diagonalModulusEncodeBHist window))
              (diagonalModulusDecodeBHist (diagonalModulusEncodeBHist readback))
              (diagonalModulusDecodeBHist (diagonalModulusEncodeBHist ledger))
              (diagonalModulusDecodeBHist (diagonalModulusEncodeBHist sealRow))
              (diagonalModulusDecodeBHist (diagonalModulusEncodeBHist provenance))
              (diagonalModulusDecodeBHist (diagonalModulusEncodeBHist nameCert))) =
            some
              (DiagonalModulusUp.mk precision threshold window readback ledger sealRow provenance
                nameCert)
        rw [DiagonalModulusTasteGate_single_carrier_alignment_decode precision,
          DiagonalModulusTasteGate_single_carrier_alignment_decode threshold,
          DiagonalModulusTasteGate_single_carrier_alignment_decode window,
          DiagonalModulusTasteGate_single_carrier_alignment_decode readback,
          DiagonalModulusTasteGate_single_carrier_alignment_decode ledger,
          DiagonalModulusTasteGate_single_carrier_alignment_decode sealRow,
          DiagonalModulusTasteGate_single_carrier_alignment_decode provenance,
          DiagonalModulusTasteGate_single_carrier_alignment_decode nameCert]
  constructor
  · intro x y heq
    have hread :
        diagonalModulusFromEventFlow (diagonalModulusToEventFlow x) =
          diagonalModulusFromEventFlow (diagonalModulusToEventFlow y) :=
      congrArg diagonalModulusFromEventFlow heq
    exact Option.some.inj
      (Eq.trans
        (DiagonalModulusTasteGate_single_carrier_alignment_round_trip x).symm
        (Eq.trans hread
          (DiagonalModulusTasteGate_single_carrier_alignment_round_trip y)))
  · rfl

end BEDC.Derived.DiagonalModulusUp
