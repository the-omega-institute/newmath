import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OsgoodUniquenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OsgoodUniquenessUp : Type where
  | mk (D I F M Q R E H C P N : BHist) : OsgoodUniquenessUp
  deriving DecidableEq

private def osgoodUniquenessEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: osgoodUniquenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: osgoodUniquenessEncodeBHist h

private def osgoodUniquenessDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (osgoodUniquenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (osgoodUniquenessDecodeBHist tail)

private theorem osgoodUniquenessDecode_encode_bhist :
    ∀ h : BHist, osgoodUniquenessDecodeBHist (osgoodUniquenessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem OsgoodUniquenessTasteGate_single_carrier_alignment_mk_congr
    {D D' I I' F F' M M' Q Q' R R' E E' H H' C C' P P' N N' : BHist}
    (hD : D' = D)
    (hI : I' = I)
    (hF : F' = F)
    (hM : M' = M)
    (hQ : Q' = Q)
    (hR : R' = R)
    (hE : E' = E)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    OsgoodUniquenessUp.mk D' I' F' M' Q' R' E' H' C' P' N' =
      OsgoodUniquenessUp.mk D I F M Q R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hD
  cases hI
  cases hF
  cases hM
  cases hQ
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private def osgoodUniquenessToEventFlow : OsgoodUniquenessUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | OsgoodUniquenessUp.mk D I F M Q R E H C P N =>
      [[BMark.b0],
        osgoodUniquenessEncodeBHist D,
        [BMark.b1, BMark.b0],
        osgoodUniquenessEncodeBHist I,
        [BMark.b1, BMark.b1, BMark.b0],
        osgoodUniquenessEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        osgoodUniquenessEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        osgoodUniquenessEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        osgoodUniquenessEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        osgoodUniquenessEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        osgoodUniquenessEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        osgoodUniquenessEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        osgoodUniquenessEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        osgoodUniquenessEncodeBHist N]

private def osgoodUniquenessFromEventFlow : EventFlow -> Option OsgoodUniquenessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | D :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | I :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | F :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | M :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | Q :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | R :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | E :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | H :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | C :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | P :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | N :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (OsgoodUniquenessUp.mk
                                                                                                  (osgoodUniquenessDecodeBHist D)
                                                                                                  (osgoodUniquenessDecodeBHist I)
                                                                                                  (osgoodUniquenessDecodeBHist F)
                                                                                                  (osgoodUniquenessDecodeBHist M)
                                                                                                  (osgoodUniquenessDecodeBHist Q)
                                                                                                  (osgoodUniquenessDecodeBHist R)
                                                                                                  (osgoodUniquenessDecodeBHist E)
                                                                                                  (osgoodUniquenessDecodeBHist H)
                                                                                                  (osgoodUniquenessDecodeBHist C)
                                                                                                  (osgoodUniquenessDecodeBHist P)
                                                                                                  (osgoodUniquenessDecodeBHist N))
                                                                                          | _ :: _ => none

private theorem OsgoodUniquenessTasteGate_single_carrier_alignment_round_trip
    (x : OsgoodUniquenessUp) :
    osgoodUniquenessFromEventFlow (osgoodUniquenessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D I F M Q R E H C P N =>
      change
        some
          (OsgoodUniquenessUp.mk
            (osgoodUniquenessDecodeBHist (osgoodUniquenessEncodeBHist D))
            (osgoodUniquenessDecodeBHist (osgoodUniquenessEncodeBHist I))
            (osgoodUniquenessDecodeBHist (osgoodUniquenessEncodeBHist F))
            (osgoodUniquenessDecodeBHist (osgoodUniquenessEncodeBHist M))
            (osgoodUniquenessDecodeBHist (osgoodUniquenessEncodeBHist Q))
            (osgoodUniquenessDecodeBHist (osgoodUniquenessEncodeBHist R))
            (osgoodUniquenessDecodeBHist (osgoodUniquenessEncodeBHist E))
            (osgoodUniquenessDecodeBHist (osgoodUniquenessEncodeBHist H))
            (osgoodUniquenessDecodeBHist (osgoodUniquenessEncodeBHist C))
            (osgoodUniquenessDecodeBHist (osgoodUniquenessEncodeBHist P))
            (osgoodUniquenessDecodeBHist (osgoodUniquenessEncodeBHist N))) =
          some (OsgoodUniquenessUp.mk D I F M Q R E H C P N)
      exact
        congrArg some
          (OsgoodUniquenessTasteGate_single_carrier_alignment_mk_congr
            (osgoodUniquenessDecode_encode_bhist D)
            (osgoodUniquenessDecode_encode_bhist I)
            (osgoodUniquenessDecode_encode_bhist F)
            (osgoodUniquenessDecode_encode_bhist M)
            (osgoodUniquenessDecode_encode_bhist Q)
            (osgoodUniquenessDecode_encode_bhist R)
            (osgoodUniquenessDecode_encode_bhist E)
            (osgoodUniquenessDecode_encode_bhist H)
            (osgoodUniquenessDecode_encode_bhist C)
            (osgoodUniquenessDecode_encode_bhist P)
            (osgoodUniquenessDecode_encode_bhist N))

private theorem OsgoodUniquenessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : OsgoodUniquenessUp} :
    osgoodUniquenessToEventFlow x = osgoodUniquenessToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      osgoodUniquenessFromEventFlow (osgoodUniquenessToEventFlow x) =
        osgoodUniquenessFromEventFlow (osgoodUniquenessToEventFlow y) :=
    congrArg osgoodUniquenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (OsgoodUniquenessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (OsgoodUniquenessTasteGate_single_carrier_alignment_round_trip y)))

instance osgoodUniquenessBHistCarrier : BHistCarrier OsgoodUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := osgoodUniquenessToEventFlow
  fromEventFlow := osgoodUniquenessFromEventFlow

instance osgoodUniquenessChapterTasteGate : ChapterTasteGate OsgoodUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change osgoodUniquenessFromEventFlow (osgoodUniquenessToEventFlow x) = some x
    exact OsgoodUniquenessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (OsgoodUniquenessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem OsgoodUniquenessTasteGate_single_carrier_alignment :
    (∀ h : BHist, osgoodUniquenessDecodeBHist (osgoodUniquenessEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier OsgoodUniquenessUp) ∧
        Nonempty (ChapterTasteGate OsgoodUniquenessUp) ∧
          osgoodUniquenessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨osgoodUniquenessDecode_encode_bhist, ⟨osgoodUniquenessBHistCarrier⟩,
      ⟨osgoodUniquenessChapterTasteGate⟩, rfl⟩

end BEDC.Derived.OsgoodUniquenessUp
