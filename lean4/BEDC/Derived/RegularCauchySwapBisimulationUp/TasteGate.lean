import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySwapBisimulationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySwapBisimulationUp : Type where
  | mk :
      (a b scheduleA scheduleB selector selectorOp modulus sealRow sealOp transports routes
        provenance localCert : BHist) →
      RegularCauchySwapBisimulationUp

private def regularCauchySwapBisimulationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySwapBisimulationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySwapBisimulationEncodeBHist h

private def regularCauchySwapBisimulationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySwapBisimulationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySwapBisimulationDecodeBHist tail)

private theorem regularCauchySwapBisimulationDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchySwapBisimulationDecodeBHist
        (regularCauchySwapBisimulationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem regularCauchySwapBisimulation_mk_congr
    {a a' b b' scheduleA scheduleA' scheduleB scheduleB' selector selector'
      selectorOp selectorOp' modulus modulus' sealRow sealRow' sealOp sealOp' transports
      transports' routes routes' provenance provenance' localCert localCert' : BHist}
    (hA : a' = a)
    (hB : b' = b)
    (hScheduleA : scheduleA' = scheduleA)
    (hScheduleB : scheduleB' = scheduleB)
    (hSelector : selector' = selector)
    (hSelectorOp : selectorOp' = selectorOp)
    (hModulus : modulus' = modulus)
    (hSeal : sealRow' = sealRow)
    (hSealOp : sealOp' = sealOp)
    (hTransports : transports' = transports)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hLocalCert : localCert' = localCert) :
    RegularCauchySwapBisimulationUp.mk a' b' scheduleA' scheduleB' selector'
        selectorOp' modulus' sealRow' sealOp' transports' routes' provenance' localCert' =
      RegularCauchySwapBisimulationUp.mk a b scheduleA scheduleB selector selectorOp
        modulus sealRow sealOp transports routes provenance localCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hA
  cases hB
  cases hScheduleA
  cases hScheduleB
  cases hSelector
  cases hSelectorOp
  cases hModulus
  cases hSeal
  cases hSealOp
  cases hTransports
  cases hRoutes
  cases hProvenance
  cases hLocalCert
  rfl

private def regularCauchySwapBisimulationToEventFlow :
    RegularCauchySwapBisimulationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySwapBisimulationUp.mk a b scheduleA scheduleB selector selectorOp
      modulus sealRow sealOp transports routes provenance localCert =>
      [regularCauchySwapBisimulationEncodeBHist a,
        regularCauchySwapBisimulationEncodeBHist b,
        regularCauchySwapBisimulationEncodeBHist scheduleA,
        regularCauchySwapBisimulationEncodeBHist scheduleB,
        regularCauchySwapBisimulationEncodeBHist selector,
        regularCauchySwapBisimulationEncodeBHist selectorOp,
        regularCauchySwapBisimulationEncodeBHist modulus,
        regularCauchySwapBisimulationEncodeBHist sealRow,
        regularCauchySwapBisimulationEncodeBHist sealOp,
        regularCauchySwapBisimulationEncodeBHist transports,
        regularCauchySwapBisimulationEncodeBHist routes,
        regularCauchySwapBisimulationEncodeBHist provenance,
        regularCauchySwapBisimulationEncodeBHist localCert]

private def regularCauchySwapBisimulationFromEventFlow :
    EventFlow → Option RegularCauchySwapBisimulationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | a :: rest0 =>
      match rest0 with
      | [] => none
      | b :: rest1 =>
          match rest1 with
          | [] => none
          | scheduleA :: rest2 =>
              match rest2 with
              | [] => none
              | scheduleB :: rest3 =>
                  match rest3 with
                  | [] => none
                  | selector :: rest4 =>
                      match rest4 with
                      | [] => none
                      | selectorOp :: rest5 =>
                          match rest5 with
                          | [] => none
                          | modulus :: rest6 =>
                              match rest6 with
                              | [] => none
                              | sealRow :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | sealOp :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transports :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | routes :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | localCert :: rest12 =>
                                                      match rest12 with
                                                      | [] =>
                                                          some
                                                            (RegularCauchySwapBisimulationUp.mk
                                                              (regularCauchySwapBisimulationDecodeBHist a)
                                                              (regularCauchySwapBisimulationDecodeBHist b)
                                                              (regularCauchySwapBisimulationDecodeBHist scheduleA)
                                                              (regularCauchySwapBisimulationDecodeBHist scheduleB)
                                                              (regularCauchySwapBisimulationDecodeBHist selector)
                                                              (regularCauchySwapBisimulationDecodeBHist selectorOp)
                                                              (regularCauchySwapBisimulationDecodeBHist modulus)
                                                              (regularCauchySwapBisimulationDecodeBHist sealRow)
                                                              (regularCauchySwapBisimulationDecodeBHist sealOp)
                                                              (regularCauchySwapBisimulationDecodeBHist transports)
                                                              (regularCauchySwapBisimulationDecodeBHist routes)
                                                              (regularCauchySwapBisimulationDecodeBHist provenance)
                                                              (regularCauchySwapBisimulationDecodeBHist localCert))
                                                      | _ :: _ => none

private theorem regularCauchySwapBisimulation_round_trip :
    ∀ x : RegularCauchySwapBisimulationUp,
      regularCauchySwapBisimulationFromEventFlow
        (regularCauchySwapBisimulationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk a b scheduleA scheduleB selector selectorOp modulus sealRow sealOp transports routes
      provenance localCert =>
      change
        some
          (RegularCauchySwapBisimulationUp.mk
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist a))
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist b))
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist scheduleA))
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist scheduleB))
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist selector))
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist selectorOp))
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist modulus))
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist sealRow))
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist sealOp))
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist transports))
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist routes))
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist provenance))
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist localCert))) =
          some
            (RegularCauchySwapBisimulationUp.mk a b scheduleA scheduleB selector
              selectorOp modulus sealRow sealOp transports routes provenance localCert)
      exact
        congrArg some
          (regularCauchySwapBisimulation_mk_congr
            (regularCauchySwapBisimulationDecode_encode_bhist a)
            (regularCauchySwapBisimulationDecode_encode_bhist b)
            (regularCauchySwapBisimulationDecode_encode_bhist scheduleA)
            (regularCauchySwapBisimulationDecode_encode_bhist scheduleB)
            (regularCauchySwapBisimulationDecode_encode_bhist selector)
            (regularCauchySwapBisimulationDecode_encode_bhist selectorOp)
            (regularCauchySwapBisimulationDecode_encode_bhist modulus)
            (regularCauchySwapBisimulationDecode_encode_bhist sealRow)
            (regularCauchySwapBisimulationDecode_encode_bhist sealOp)
            (regularCauchySwapBisimulationDecode_encode_bhist transports)
            (regularCauchySwapBisimulationDecode_encode_bhist routes)
            (regularCauchySwapBisimulationDecode_encode_bhist provenance)
            (regularCauchySwapBisimulationDecode_encode_bhist localCert))

private theorem regularCauchySwapBisimulationToEventFlow_injective
    {x y : RegularCauchySwapBisimulationUp} :
    regularCauchySwapBisimulationToEventFlow x =
      regularCauchySwapBisimulationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySwapBisimulationFromEventFlow
          (regularCauchySwapBisimulationToEventFlow x) =
        regularCauchySwapBisimulationFromEventFlow
          (regularCauchySwapBisimulationToEventFlow y) :=
    congrArg regularCauchySwapBisimulationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchySwapBisimulation_round_trip x).symm
      (Eq.trans hread (regularCauchySwapBisimulation_round_trip y)))

instance regularCauchySwapBisimulationBHistCarrier :
    BHistCarrier RegularCauchySwapBisimulationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySwapBisimulationToEventFlow
  fromEventFlow := regularCauchySwapBisimulationFromEventFlow

instance regularCauchySwapBisimulationChapterTasteGate :
    ChapterTasteGate RegularCauchySwapBisimulationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchySwapBisimulationFromEventFlow
        (regularCauchySwapBisimulationToEventFlow x) = some x
    exact regularCauchySwapBisimulation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchySwapBisimulationToEventFlow_injective heq)

theorem RegularCauchySwapBisimulationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchySwapBisimulationDecodeBHist
        (regularCauchySwapBisimulationEncodeBHist h) = h) ∧
      (∀ x : RegularCauchySwapBisimulationUp,
        regularCauchySwapBisimulationFromEventFlow
          (regularCauchySwapBisimulationToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchySwapBisimulationUp,
          regularCauchySwapBisimulationToEventFlow x =
            regularCauchySwapBisimulationToEventFlow y → x = y) ∧
          regularCauchySwapBisimulationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchySwapBisimulationDecode_encode_bhist
  · constructor
    · exact regularCauchySwapBisimulation_round_trip
    · constructor
      · intro x y heq
        exact regularCauchySwapBisimulationToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchySwapBisimulationUp
