import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GroundCompilerFlowLevelRoundTripUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GroundCompilerFlowLevelRoundTripUp : Type where
  | mk :
      (source encoding decoder legal transport route component continuation provenance name :
        BHist) →
      GroundCompilerFlowLevelRoundTripUp
  deriving DecidableEq

def groundCompilerFlowLevelRoundTripEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: groundCompilerFlowLevelRoundTripEncodeBHist h
  | BHist.e1 h => BMark.b1 :: groundCompilerFlowLevelRoundTripEncodeBHist h

def groundCompilerFlowLevelRoundTripDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (groundCompilerFlowLevelRoundTripDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (groundCompilerFlowLevelRoundTripDecodeBHist tail)

private theorem groundCompilerFlowLevelRoundTripDecode_encode :
    ∀ h : BHist,
      groundCompilerFlowLevelRoundTripDecodeBHist
        (groundCompilerFlowLevelRoundTripEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def groundCompilerFlowLevelRoundTripFields :
    GroundCompilerFlowLevelRoundTripUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GroundCompilerFlowLevelRoundTripUp.mk S E D L T R H C P N =>
      [S, E, D, L, T, R, H, C, P, N]

def groundCompilerFlowLevelRoundTripToEventFlow :
    GroundCompilerFlowLevelRoundTripUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | GroundCompilerFlowLevelRoundTripUp.mk S E D L T R H C P N =>
      [groundCompilerFlowLevelRoundTripEncodeBHist S,
        groundCompilerFlowLevelRoundTripEncodeBHist E,
        groundCompilerFlowLevelRoundTripEncodeBHist D,
        groundCompilerFlowLevelRoundTripEncodeBHist L,
        groundCompilerFlowLevelRoundTripEncodeBHist T,
        groundCompilerFlowLevelRoundTripEncodeBHist R,
        groundCompilerFlowLevelRoundTripEncodeBHist H,
        groundCompilerFlowLevelRoundTripEncodeBHist C,
        groundCompilerFlowLevelRoundTripEncodeBHist P,
        groundCompilerFlowLevelRoundTripEncodeBHist N]

def groundCompilerFlowLevelRoundTripFromEventFlow :
    EventFlow → Option GroundCompilerFlowLevelRoundTripUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: restS =>
      match restS with
      | [] => none
      | E :: restE =>
          match restE with
          | [] => none
          | D :: restD =>
              match restD with
              | [] => none
              | L :: restL =>
                  match restL with
                  | [] => none
                  | T :: restT =>
                      match restT with
                      | [] => none
                      | R :: restR =>
                          match restR with
                          | [] => none
                          | H :: restH =>
                              match restH with
                              | [] => none
                              | C :: restC =>
                                  match restC with
                                  | [] => none
                                  | P :: restP =>
                                      match restP with
                                      | [] => none
                                      | N :: restN =>
                                          match restN with
                                          | [] =>
                                              some
                                                (GroundCompilerFlowLevelRoundTripUp.mk
                                                  (groundCompilerFlowLevelRoundTripDecodeBHist S)
                                                  (groundCompilerFlowLevelRoundTripDecodeBHist E)
                                                  (groundCompilerFlowLevelRoundTripDecodeBHist D)
                                                  (groundCompilerFlowLevelRoundTripDecodeBHist L)
                                                  (groundCompilerFlowLevelRoundTripDecodeBHist T)
                                                  (groundCompilerFlowLevelRoundTripDecodeBHist R)
                                                  (groundCompilerFlowLevelRoundTripDecodeBHist H)
                                                  (groundCompilerFlowLevelRoundTripDecodeBHist C)
                                                  (groundCompilerFlowLevelRoundTripDecodeBHist P)
                                                  (groundCompilerFlowLevelRoundTripDecodeBHist N))
                                          | _ :: _ => none

private theorem groundCompilerFlowLevelRoundTrip_round_trip :
    ∀ x : GroundCompilerFlowLevelRoundTripUp,
      groundCompilerFlowLevelRoundTripFromEventFlow
        (groundCompilerFlowLevelRoundTripToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S E D L T R H C P N =>
      exact congrArg some
        (Eq.ndrec
          (motive := fun z =>
            GroundCompilerFlowLevelRoundTripUp.mk
                (groundCompilerFlowLevelRoundTripDecodeBHist
                  (groundCompilerFlowLevelRoundTripEncodeBHist S))
                (groundCompilerFlowLevelRoundTripDecodeBHist
                  (groundCompilerFlowLevelRoundTripEncodeBHist E))
                (groundCompilerFlowLevelRoundTripDecodeBHist
                  (groundCompilerFlowLevelRoundTripEncodeBHist D))
                (groundCompilerFlowLevelRoundTripDecodeBHist
                  (groundCompilerFlowLevelRoundTripEncodeBHist L))
                (groundCompilerFlowLevelRoundTripDecodeBHist
                  (groundCompilerFlowLevelRoundTripEncodeBHist T))
                (groundCompilerFlowLevelRoundTripDecodeBHist
                  (groundCompilerFlowLevelRoundTripEncodeBHist R))
                (groundCompilerFlowLevelRoundTripDecodeBHist
                  (groundCompilerFlowLevelRoundTripEncodeBHist H))
                (groundCompilerFlowLevelRoundTripDecodeBHist
                  (groundCompilerFlowLevelRoundTripEncodeBHist C))
                (groundCompilerFlowLevelRoundTripDecodeBHist
                  (groundCompilerFlowLevelRoundTripEncodeBHist P)) z =
              GroundCompilerFlowLevelRoundTripUp.mk S E D L T R H C P N)
          (Eq.ndrec
            (motive := fun z =>
              GroundCompilerFlowLevelRoundTripUp.mk
                  (groundCompilerFlowLevelRoundTripDecodeBHist
                    (groundCompilerFlowLevelRoundTripEncodeBHist S))
                  (groundCompilerFlowLevelRoundTripDecodeBHist
                    (groundCompilerFlowLevelRoundTripEncodeBHist E))
                  (groundCompilerFlowLevelRoundTripDecodeBHist
                    (groundCompilerFlowLevelRoundTripEncodeBHist D))
                  (groundCompilerFlowLevelRoundTripDecodeBHist
                    (groundCompilerFlowLevelRoundTripEncodeBHist L))
                  (groundCompilerFlowLevelRoundTripDecodeBHist
                    (groundCompilerFlowLevelRoundTripEncodeBHist T))
                  (groundCompilerFlowLevelRoundTripDecodeBHist
                    (groundCompilerFlowLevelRoundTripEncodeBHist R))
                  (groundCompilerFlowLevelRoundTripDecodeBHist
                    (groundCompilerFlowLevelRoundTripEncodeBHist H))
                  (groundCompilerFlowLevelRoundTripDecodeBHist
                    (groundCompilerFlowLevelRoundTripEncodeBHist C)) z N =
                GroundCompilerFlowLevelRoundTripUp.mk S E D L T R H C P N)
            (Eq.ndrec
              (motive := fun z =>
                GroundCompilerFlowLevelRoundTripUp.mk
                    (groundCompilerFlowLevelRoundTripDecodeBHist
                      (groundCompilerFlowLevelRoundTripEncodeBHist S))
                    (groundCompilerFlowLevelRoundTripDecodeBHist
                      (groundCompilerFlowLevelRoundTripEncodeBHist E))
                    (groundCompilerFlowLevelRoundTripDecodeBHist
                      (groundCompilerFlowLevelRoundTripEncodeBHist D))
                    (groundCompilerFlowLevelRoundTripDecodeBHist
                      (groundCompilerFlowLevelRoundTripEncodeBHist L))
                    (groundCompilerFlowLevelRoundTripDecodeBHist
                      (groundCompilerFlowLevelRoundTripEncodeBHist T))
                    (groundCompilerFlowLevelRoundTripDecodeBHist
                      (groundCompilerFlowLevelRoundTripEncodeBHist R))
                    (groundCompilerFlowLevelRoundTripDecodeBHist
                      (groundCompilerFlowLevelRoundTripEncodeBHist H)) z P N =
                  GroundCompilerFlowLevelRoundTripUp.mk S E D L T R H C P N)
              (Eq.ndrec
                (motive := fun z =>
                  GroundCompilerFlowLevelRoundTripUp.mk
                      (groundCompilerFlowLevelRoundTripDecodeBHist
                        (groundCompilerFlowLevelRoundTripEncodeBHist S))
                      (groundCompilerFlowLevelRoundTripDecodeBHist
                        (groundCompilerFlowLevelRoundTripEncodeBHist E))
                      (groundCompilerFlowLevelRoundTripDecodeBHist
                        (groundCompilerFlowLevelRoundTripEncodeBHist D))
                      (groundCompilerFlowLevelRoundTripDecodeBHist
                        (groundCompilerFlowLevelRoundTripEncodeBHist L))
                      (groundCompilerFlowLevelRoundTripDecodeBHist
                        (groundCompilerFlowLevelRoundTripEncodeBHist T))
                      (groundCompilerFlowLevelRoundTripDecodeBHist
                        (groundCompilerFlowLevelRoundTripEncodeBHist R)) z C P N =
                    GroundCompilerFlowLevelRoundTripUp.mk S E D L T R H C P N)
                (Eq.ndrec
                  (motive := fun z =>
                    GroundCompilerFlowLevelRoundTripUp.mk
                        (groundCompilerFlowLevelRoundTripDecodeBHist
                          (groundCompilerFlowLevelRoundTripEncodeBHist S))
                        (groundCompilerFlowLevelRoundTripDecodeBHist
                          (groundCompilerFlowLevelRoundTripEncodeBHist E))
                        (groundCompilerFlowLevelRoundTripDecodeBHist
                          (groundCompilerFlowLevelRoundTripEncodeBHist D))
                        (groundCompilerFlowLevelRoundTripDecodeBHist
                          (groundCompilerFlowLevelRoundTripEncodeBHist L))
                        (groundCompilerFlowLevelRoundTripDecodeBHist
                          (groundCompilerFlowLevelRoundTripEncodeBHist T)) z H C P N =
                      GroundCompilerFlowLevelRoundTripUp.mk S E D L T R H C P N)
                  (Eq.ndrec
                    (motive := fun z =>
                      GroundCompilerFlowLevelRoundTripUp.mk
                          (groundCompilerFlowLevelRoundTripDecodeBHist
                            (groundCompilerFlowLevelRoundTripEncodeBHist S))
                          (groundCompilerFlowLevelRoundTripDecodeBHist
                            (groundCompilerFlowLevelRoundTripEncodeBHist E))
                          (groundCompilerFlowLevelRoundTripDecodeBHist
                            (groundCompilerFlowLevelRoundTripEncodeBHist D))
                          (groundCompilerFlowLevelRoundTripDecodeBHist
                            (groundCompilerFlowLevelRoundTripEncodeBHist L)) z R H C P N =
                        GroundCompilerFlowLevelRoundTripUp.mk S E D L T R H C P N)
                    (Eq.ndrec
                      (motive := fun z =>
                        GroundCompilerFlowLevelRoundTripUp.mk
                            (groundCompilerFlowLevelRoundTripDecodeBHist
                              (groundCompilerFlowLevelRoundTripEncodeBHist S))
                            (groundCompilerFlowLevelRoundTripDecodeBHist
                              (groundCompilerFlowLevelRoundTripEncodeBHist E))
                            (groundCompilerFlowLevelRoundTripDecodeBHist
                              (groundCompilerFlowLevelRoundTripEncodeBHist D)) z T R H C P N =
                          GroundCompilerFlowLevelRoundTripUp.mk S E D L T R H C P N)
                      (Eq.ndrec
                        (motive := fun z =>
                          GroundCompilerFlowLevelRoundTripUp.mk
                              (groundCompilerFlowLevelRoundTripDecodeBHist
                                (groundCompilerFlowLevelRoundTripEncodeBHist S))
                              (groundCompilerFlowLevelRoundTripDecodeBHist
                                (groundCompilerFlowLevelRoundTripEncodeBHist E)) z L T R H C P N =
                            GroundCompilerFlowLevelRoundTripUp.mk S E D L T R H C P N)
                        (Eq.ndrec
                          (motive := fun z =>
                            GroundCompilerFlowLevelRoundTripUp.mk
                                (groundCompilerFlowLevelRoundTripDecodeBHist
                                  (groundCompilerFlowLevelRoundTripEncodeBHist S)) z D L T R H C P N =
                              GroundCompilerFlowLevelRoundTripUp.mk S E D L T R H C P N)
                          (Eq.ndrec
                            (motive := fun z =>
                              GroundCompilerFlowLevelRoundTripUp.mk z E D L T R H C P N =
                                GroundCompilerFlowLevelRoundTripUp.mk S E D L T R H C P N)
                            rfl
                            (groundCompilerFlowLevelRoundTripDecode_encode S).symm)
                          (groundCompilerFlowLevelRoundTripDecode_encode E).symm)
                        (groundCompilerFlowLevelRoundTripDecode_encode D).symm)
                      (groundCompilerFlowLevelRoundTripDecode_encode L).symm)
                    (groundCompilerFlowLevelRoundTripDecode_encode T).symm)
                  (groundCompilerFlowLevelRoundTripDecode_encode R).symm)
                (groundCompilerFlowLevelRoundTripDecode_encode H).symm)
              (groundCompilerFlowLevelRoundTripDecode_encode C).symm)
            (groundCompilerFlowLevelRoundTripDecode_encode P).symm)
          (groundCompilerFlowLevelRoundTripDecode_encode N).symm)

private theorem groundCompilerFlowLevelRoundTripToEventFlow_injective
    {x y : GroundCompilerFlowLevelRoundTripUp} :
    groundCompilerFlowLevelRoundTripToEventFlow x =
      groundCompilerFlowLevelRoundTripToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      groundCompilerFlowLevelRoundTripFromEventFlow
          (groundCompilerFlowLevelRoundTripToEventFlow x) =
        groundCompilerFlowLevelRoundTripFromEventFlow
          (groundCompilerFlowLevelRoundTripToEventFlow y) :=
    congrArg groundCompilerFlowLevelRoundTripFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (groundCompilerFlowLevelRoundTrip_round_trip x).symm
      (Eq.trans hread (groundCompilerFlowLevelRoundTrip_round_trip y)))

private theorem groundCompilerFlowLevelRoundTrip_field_faithful :
    ∀ x y : GroundCompilerFlowLevelRoundTripUp,
      groundCompilerFlowLevelRoundTripFields x =
        groundCompilerFlowLevelRoundTripFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk S1 E1 D1 L1 T1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 E2 D2 L2 T2 R2 H2 C2 P2 N2 =>
          injection h with hS t1
          injection t1 with hE t2
          injection t2 with hD t3
          injection t3 with hL t4
          injection t4 with hT t5
          injection t5 with hR t6
          injection t6 with hH t7
          injection t7 with hC t8
          injection t8 with hP t9
          injection t9 with hN _
          subst hS
          subst hE
          subst hD
          subst hL
          subst hT
          subst hR
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance groundCompilerFlowLevelRoundTripBHistCarrier :
    BHistCarrier GroundCompilerFlowLevelRoundTripUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := groundCompilerFlowLevelRoundTripToEventFlow
  fromEventFlow := groundCompilerFlowLevelRoundTripFromEventFlow

instance groundCompilerFlowLevelRoundTripChapterTasteGate :
    ChapterTasteGate GroundCompilerFlowLevelRoundTripUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      groundCompilerFlowLevelRoundTripFromEventFlow
          (groundCompilerFlowLevelRoundTripToEventFlow x) =
        some x
    exact groundCompilerFlowLevelRoundTrip_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (groundCompilerFlowLevelRoundTripToEventFlow_injective heq)

instance groundCompilerFlowLevelRoundTripFieldFaithful :
    FieldFaithful GroundCompilerFlowLevelRoundTripUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := groundCompilerFlowLevelRoundTripFields
  field_faithful := groundCompilerFlowLevelRoundTrip_field_faithful

instance groundCompilerFlowLevelRoundTripNontrivial :
    Nontrivial GroundCompilerFlowLevelRoundTripUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨GroundCompilerFlowLevelRoundTripUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      GroundCompilerFlowLevelRoundTripUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate GroundCompilerFlowLevelRoundTripUp :=
  -- BEDC touchpoint anchor: BHist BMark
  groundCompilerFlowLevelRoundTripChapterTasteGate

theorem GroundCompilerFlowLevelRoundTripTasteGate_single_carrier_alignment :
    (forall h : BHist,
        groundCompilerFlowLevelRoundTripDecodeBHist
          (groundCompilerFlowLevelRoundTripEncodeBHist h) = h) /\
      (forall x : GroundCompilerFlowLevelRoundTripUp,
        groundCompilerFlowLevelRoundTripFromEventFlow
          (groundCompilerFlowLevelRoundTripToEventFlow x) = some x) /\
        (forall x y : GroundCompilerFlowLevelRoundTripUp,
          groundCompilerFlowLevelRoundTripToEventFlow x =
            groundCompilerFlowLevelRoundTripToEventFlow y ->
            x = y) /\
          groundCompilerFlowLevelRoundTripEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact groundCompilerFlowLevelRoundTripDecode_encode
  · constructor
    · exact groundCompilerFlowLevelRoundTrip_round_trip
    · constructor
      · intro x y heq
        exact groundCompilerFlowLevelRoundTripToEventFlow_injective heq
      · rfl

end BEDC.Derived.GroundCompilerFlowLevelRoundTripUp
