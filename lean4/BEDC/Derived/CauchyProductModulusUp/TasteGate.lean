import BEDC.Derived.CauchyProductModulusUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyProductModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def cauchyProductModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyProductModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyProductModulusEncodeBHist h

def cauchyProductModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyProductModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyProductModulusDecodeBHist tail)

private theorem cauchyProductModulus_decode_encode_bhist :
    ∀ h : BHist,
      cauchyProductModulusDecodeBHist (cauchyProductModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyProductModulusFields : BEDC.Derived.CauchyProductModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.CauchyProductModulusUp.mk sourceA sourceB windowA windowB dyadicA dyadicB
      budget modulus readback sealRow transport routes provenance name =>
      [sourceA, sourceB, windowA, windowB, dyadicA, dyadicB, budget, modulus,
        readback, sealRow, transport, routes, provenance, name]

def cauchyProductModulusToEventFlow :
    BEDC.Derived.CauchyProductModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyProductModulusFields x).map cauchyProductModulusEncodeBHist

private def cauchyProductModulusEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyProductModulusEventAt index rest

private def cauchyProductModulusLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => true
  | Nat.zero, _event :: _rest => false
  | Nat.succ _index, [] => false
  | Nat.succ index, _event :: rest => cauchyProductModulusLengthEq index rest

def cauchyProductModulusFromEventFlow :
    EventFlow → Option BEDC.Derived.CauchyProductModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match cauchyProductModulusLengthEq 14 flow with
      | true =>
          some
            (BEDC.Derived.CauchyProductModulusUp.mk
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 0 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 1 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 2 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 3 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 4 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 5 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 6 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 7 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 8 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 9 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 10 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 11 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 12 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 13 flow)))
      | false => none

private theorem cauchyProductModulus_mk_congr
    {sourceA sourceA' sourceB sourceB' windowA windowA' windowB windowB'
      dyadicA dyadicA' dyadicB dyadicB' budget budget' modulus modulus'
      readback readback' sealRow sealRow' transport transport' routes routes'
      provenance provenance' name name' : BHist}
    (hSourceA : sourceA' = sourceA) (hSourceB : sourceB' = sourceB)
    (hWindowA : windowA' = windowA) (hWindowB : windowB' = windowB)
    (hDyadicA : dyadicA' = dyadicA) (hDyadicB : dyadicB' = dyadicB)
    (hBudget : budget' = budget) (hModulus : modulus' = modulus)
    (hReadback : readback' = readback) (hSealRow : sealRow' = sealRow)
    (hTransport : transport' = transport) (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance) (hName : name' = name) :
    BEDC.Derived.CauchyProductModulusUp.mk sourceA' sourceB' windowA' windowB'
        dyadicA' dyadicB' budget' modulus' readback' sealRow' transport' routes'
        provenance' name' =
      BEDC.Derived.CauchyProductModulusUp.mk sourceA sourceB windowA windowB
        dyadicA dyadicB budget modulus readback sealRow transport routes provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSourceA
  cases hSourceB
  cases hWindowA
  cases hWindowB
  cases hDyadicA
  cases hDyadicB
  cases hBudget
  cases hModulus
  cases hReadback
  cases hSealRow
  cases hTransport
  cases hRoutes
  cases hProvenance
  cases hName
  rfl

private theorem cauchyProductModulus_round_trip :
    ∀ x : BEDC.Derived.CauchyProductModulusUp,
      cauchyProductModulusFromEventFlow (cauchyProductModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceA sourceB windowA windowB dyadicA dyadicB budget modulus readback sealRow
      transport routes provenance name =>
      exact
        congrArg some
          (cauchyProductModulus_mk_congr
            (cauchyProductModulus_decode_encode_bhist sourceA)
            (cauchyProductModulus_decode_encode_bhist sourceB)
            (cauchyProductModulus_decode_encode_bhist windowA)
            (cauchyProductModulus_decode_encode_bhist windowB)
            (cauchyProductModulus_decode_encode_bhist dyadicA)
            (cauchyProductModulus_decode_encode_bhist dyadicB)
            (cauchyProductModulus_decode_encode_bhist budget)
            (cauchyProductModulus_decode_encode_bhist modulus)
            (cauchyProductModulus_decode_encode_bhist readback)
            (cauchyProductModulus_decode_encode_bhist sealRow)
            (cauchyProductModulus_decode_encode_bhist transport)
            (cauchyProductModulus_decode_encode_bhist routes)
            (cauchyProductModulus_decode_encode_bhist provenance)
            (cauchyProductModulus_decode_encode_bhist name))

private theorem cauchyProductModulusToEventFlow_injective
    {x y : BEDC.Derived.CauchyProductModulusUp} :
    cauchyProductModulusToEventFlow x = cauchyProductModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyProductModulusFromEventFlow (cauchyProductModulusToEventFlow x) =
        cauchyProductModulusFromEventFlow (cauchyProductModulusToEventFlow y) :=
    congrArg cauchyProductModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyProductModulus_round_trip x).symm
      (Eq.trans hread (cauchyProductModulus_round_trip y)))

instance cauchyProductModulusBHistCarrier :
    BHistCarrier BEDC.Derived.CauchyProductModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyProductModulusToEventFlow
  fromEventFlow := cauchyProductModulusFromEventFlow

instance cauchyProductModulusChapterTasteGate :
    ChapterTasteGate BEDC.Derived.CauchyProductModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyProductModulusFromEventFlow (cauchyProductModulusToEventFlow x) = some x
    exact cauchyProductModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyProductModulusToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BEDC.Derived.CauchyProductModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyProductModulusChapterTasteGate

theorem CauchyProductModulusTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BEDC.Derived.CauchyProductModulusUp) ∧
      (∀ h : BHist, cauchyProductModulusDecodeBHist (cauchyProductModulusEncodeBHist h) = h) ∧
        (∀ x : BEDC.Derived.CauchyProductModulusUp,
          cauchyProductModulusFromEventFlow (cauchyProductModulusToEventFlow x) = some x) ∧
          (∀ x y : BEDC.Derived.CauchyProductModulusUp,
            cauchyProductModulusToEventFlow x = cauchyProductModulusToEventFlow y -> x = y) ∧
            cauchyProductModulusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨cauchyProductModulusChapterTasteGate⟩,
      cauchyProductModulus_decode_encode_bhist,
      cauchyProductModulus_round_trip,
      (fun _ _ heq => cauchyProductModulusToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyProductModulusUp
