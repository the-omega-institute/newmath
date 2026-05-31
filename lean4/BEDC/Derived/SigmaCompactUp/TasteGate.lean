import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SigmaCompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SigmaCompactUp : Type where
  | mk
      (source exhaustion compactWitness boundary localSupport transport replay
        provenance nameCert : BHist) :
      SigmaCompactUp
  deriving DecidableEq

def sigmaCompactEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sigmaCompactEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sigmaCompactEncodeBHist h

def sigmaCompactDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sigmaCompactDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sigmaCompactDecodeBHist tail)

private theorem sigmaCompactDecode_encode_bhist :
    ∀ h : BHist, sigmaCompactDecodeBHist (sigmaCompactEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem sigmaCompact_mk_congr
    {source source' exhaustion exhaustion' compactWitness compactWitness'
      boundary boundary' localSupport localSupport' transport transport'
      replay replay' provenance provenance' nameCert nameCert' : BHist}
    (hSource : source' = source)
    (hExhaustion : exhaustion' = exhaustion)
    (hCompactWitness : compactWitness' = compactWitness)
    (hBoundary : boundary' = boundary)
    (hLocalSupport : localSupport' = localSupport)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    SigmaCompactUp.mk source' exhaustion' compactWitness' boundary' localSupport'
        transport' replay' provenance' nameCert' =
      SigmaCompactUp.mk source exhaustion compactWitness boundary localSupport
        transport replay provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSource
  cases hExhaustion
  cases hCompactWitness
  cases hBoundary
  cases hLocalSupport
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hNameCert
  rfl

def sigmaCompactToEventFlow : SigmaCompactUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SigmaCompactUp.mk source exhaustion compactWitness boundary localSupport
      transport replay provenance nameCert =>
      [[BMark.b0],
        sigmaCompactEncodeBHist source,
        [BMark.b1, BMark.b0],
        sigmaCompactEncodeBHist exhaustion,
        [BMark.b1, BMark.b1, BMark.b0],
        sigmaCompactEncodeBHist compactWitness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        sigmaCompactEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        sigmaCompactEncodeBHist localSupport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        sigmaCompactEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        sigmaCompactEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        sigmaCompactEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        sigmaCompactEncodeBHist nameCert]

private def sigmaCompactEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | _, [] => []
  | 0, row :: _ => row
  | n + 1, _ :: rows => sigmaCompactEventAtDefault n rows

def sigmaCompactFromEventFlow (ef : EventFlow) : Option SigmaCompactUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef.length with
  | 18 =>
      some
        (SigmaCompactUp.mk
          (sigmaCompactDecodeBHist (sigmaCompactEventAtDefault 1 ef))
          (sigmaCompactDecodeBHist (sigmaCompactEventAtDefault 3 ef))
          (sigmaCompactDecodeBHist (sigmaCompactEventAtDefault 5 ef))
          (sigmaCompactDecodeBHist (sigmaCompactEventAtDefault 7 ef))
          (sigmaCompactDecodeBHist (sigmaCompactEventAtDefault 9 ef))
          (sigmaCompactDecodeBHist (sigmaCompactEventAtDefault 11 ef))
          (sigmaCompactDecodeBHist (sigmaCompactEventAtDefault 13 ef))
          (sigmaCompactDecodeBHist (sigmaCompactEventAtDefault 15 ef))
          (sigmaCompactDecodeBHist (sigmaCompactEventAtDefault 17 ef)))
  | _ => none

private theorem sigmaCompact_round_trip :
    ∀ x : SigmaCompactUp,
      sigmaCompactFromEventFlow (sigmaCompactToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source exhaustion compactWitness boundary localSupport transport replay provenance nameCert =>
      change
        some
          (SigmaCompactUp.mk
            (sigmaCompactDecodeBHist (sigmaCompactEncodeBHist source))
            (sigmaCompactDecodeBHist (sigmaCompactEncodeBHist exhaustion))
            (sigmaCompactDecodeBHist (sigmaCompactEncodeBHist compactWitness))
            (sigmaCompactDecodeBHist (sigmaCompactEncodeBHist boundary))
            (sigmaCompactDecodeBHist (sigmaCompactEncodeBHist localSupport))
            (sigmaCompactDecodeBHist (sigmaCompactEncodeBHist transport))
            (sigmaCompactDecodeBHist (sigmaCompactEncodeBHist replay))
            (sigmaCompactDecodeBHist (sigmaCompactEncodeBHist provenance))
            (sigmaCompactDecodeBHist (sigmaCompactEncodeBHist nameCert))) =
          some
            (SigmaCompactUp.mk source exhaustion compactWitness boundary
              localSupport transport replay provenance nameCert)
      exact
        congrArg some
          (sigmaCompact_mk_congr
            (sigmaCompactDecode_encode_bhist source)
            (sigmaCompactDecode_encode_bhist exhaustion)
            (sigmaCompactDecode_encode_bhist compactWitness)
            (sigmaCompactDecode_encode_bhist boundary)
            (sigmaCompactDecode_encode_bhist localSupport)
            (sigmaCompactDecode_encode_bhist transport)
            (sigmaCompactDecode_encode_bhist replay)
            (sigmaCompactDecode_encode_bhist provenance)
            (sigmaCompactDecode_encode_bhist nameCert))

private theorem sigmaCompactToEventFlow_injective {x y : SigmaCompactUp} :
    sigmaCompactToEventFlow x = sigmaCompactToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sigmaCompactFromEventFlow (sigmaCompactToEventFlow x) =
        sigmaCompactFromEventFlow (sigmaCompactToEventFlow y) :=
    congrArg sigmaCompactFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (sigmaCompact_round_trip x).symm
      (Eq.trans hread (sigmaCompact_round_trip y)))

instance sigmaCompactBHistCarrier : BHistCarrier SigmaCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sigmaCompactToEventFlow
  fromEventFlow := sigmaCompactFromEventFlow

instance sigmaCompactChapterTasteGate : ChapterTasteGate SigmaCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sigmaCompactFromEventFlow (sigmaCompactToEventFlow x) = some x
    exact sigmaCompact_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sigmaCompactToEventFlow_injective heq)

theorem SigmaCompactTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SigmaCompactUp) ∧
      (∀ h : BHist, sigmaCompactDecodeBHist (sigmaCompactEncodeBHist h) = h) ∧
        (∀ x : SigmaCompactUp,
          sigmaCompactFromEventFlow (sigmaCompactToEventFlow x) = some x) ∧
          sigmaCompactEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨sigmaCompactChapterTasteGate⟩
  · constructor
    · exact sigmaCompactDecode_encode_bhist
    · constructor
      · exact sigmaCompact_round_trip
      · rfl

end BEDC.Derived.SigmaCompactUp
