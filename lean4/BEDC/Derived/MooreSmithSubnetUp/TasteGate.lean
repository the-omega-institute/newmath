import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MooreSmithSubnetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MooreSmithSubnetUp : Type where
  | mk : (I J phi A T W D R E H C P N : BHist) → MooreSmithSubnetUp
  deriving DecidableEq

def mooreSmithSubnetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: mooreSmithSubnetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: mooreSmithSubnetEncodeBHist h

def mooreSmithSubnetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (mooreSmithSubnetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (mooreSmithSubnetDecodeBHist tail)

private theorem mooreSmithSubnet_decode_encode :
    ∀ h : BHist, mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def mooreSmithSubnetFields : MooreSmithSubnetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MooreSmithSubnetUp.mk I J phi A T W D R E H C P N =>
      [I, J, phi, A, T, W, D, R, E, H, C, P, N]

def mooreSmithSubnetToEventFlow : MooreSmithSubnetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (mooreSmithSubnetFields x).map mooreSmithSubnetEncodeBHist

def mooreSmithSubnetFromEventFlow : EventFlow → Option MooreSmithSubnetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | I :: rest0 =>
      match rest0 with
      | [] => none
      | J :: rest1 =>
          match rest1 with
          | [] => none
          | phi :: rest2 =>
              match rest2 with
              | [] => none
              | A :: rest3 =>
                  match rest3 with
                  | [] => none
                  | T :: rest4 =>
                      match rest4 with
                      | [] => none
                      | W :: rest5 =>
                          match rest5 with
                          | [] => none
                          | D :: rest6 =>
                              match rest6 with
                              | [] => none
                              | R :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | E :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | H :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | C :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | P :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | N :: rest12 =>
                                                      match rest12 with
                                                      | [] =>
                                                          some
                                                            (MooreSmithSubnetUp.mk
                                                              (mooreSmithSubnetDecodeBHist I)
                                                              (mooreSmithSubnetDecodeBHist J)
                                                              (mooreSmithSubnetDecodeBHist phi)
                                                              (mooreSmithSubnetDecodeBHist A)
                                                              (mooreSmithSubnetDecodeBHist T)
                                                              (mooreSmithSubnetDecodeBHist W)
                                                              (mooreSmithSubnetDecodeBHist D)
                                                              (mooreSmithSubnetDecodeBHist R)
                                                              (mooreSmithSubnetDecodeBHist E)
                                                              (mooreSmithSubnetDecodeBHist H)
                                                              (mooreSmithSubnetDecodeBHist C)
                                                              (mooreSmithSubnetDecodeBHist P)
                                                              (mooreSmithSubnetDecodeBHist N))
                                                      | _ :: _ => none

private theorem mooreSmithSubnet_round_trip :
    ∀ x : MooreSmithSubnetUp,
      mooreSmithSubnetFromEventFlow (mooreSmithSubnetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I J phi A T W D R E H C P N =>
      change
        some
          (MooreSmithSubnetUp.mk
            (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist I))
            (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist J))
            (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist phi))
            (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist A))
            (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist T))
            (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist W))
            (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist D))
            (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist R))
            (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist E))
            (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist H))
            (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist C))
            (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist P))
            (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist N))) =
          some (MooreSmithSubnetUp.mk I J phi A T W D R E H C P N)
      rw [mooreSmithSubnet_decode_encode I, mooreSmithSubnet_decode_encode J,
        mooreSmithSubnet_decode_encode phi, mooreSmithSubnet_decode_encode A,
        mooreSmithSubnet_decode_encode T, mooreSmithSubnet_decode_encode W,
        mooreSmithSubnet_decode_encode D, mooreSmithSubnet_decode_encode R,
        mooreSmithSubnet_decode_encode E, mooreSmithSubnet_decode_encode H,
        mooreSmithSubnet_decode_encode C, mooreSmithSubnet_decode_encode P,
        mooreSmithSubnet_decode_encode N]

private theorem mooreSmithSubnetToEventFlow_injective {x y : MooreSmithSubnetUp} :
    mooreSmithSubnetToEventFlow x = mooreSmithSubnetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      mooreSmithSubnetFromEventFlow (mooreSmithSubnetToEventFlow x) =
        mooreSmithSubnetFromEventFlow (mooreSmithSubnetToEventFlow y) :=
    congrArg mooreSmithSubnetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (mooreSmithSubnet_round_trip x).symm
      (Eq.trans hread (mooreSmithSubnet_round_trip y)))

private theorem mooreSmithSubnet_fields_faithful :
    ∀ x y : MooreSmithSubnetUp, mooreSmithSubnetFields x = mooreSmithSubnetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk I1 J1 phi1 A1 T1 W1 D1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 J2 phi2 A2 T2 W2 D2 R2 E2 H2 C2 P2 N2 =>
          injection h with hI t1
          injection t1 with hJ t2
          injection t2 with hPhi t3
          injection t3 with hA t4
          injection t4 with hT t5
          injection t5 with hW t6
          injection t6 with hD t7
          injection t7 with hR t8
          injection t8 with hE t9
          injection t9 with hH t10
          injection t10 with hC t11
          injection t11 with hP t12
          injection t12 with hN _
          subst hI
          subst hJ
          subst hPhi
          subst hA
          subst hT
          subst hW
          subst hD
          subst hR
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance mooreSmithSubnetBHistCarrier : BHistCarrier MooreSmithSubnetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := mooreSmithSubnetToEventFlow
  fromEventFlow := mooreSmithSubnetFromEventFlow

instance mooreSmithSubnetChapterTasteGate : ChapterTasteGate MooreSmithSubnetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change mooreSmithSubnetFromEventFlow (mooreSmithSubnetToEventFlow x) = some x
    exact mooreSmithSubnet_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (mooreSmithSubnetToEventFlow_injective heq)

instance mooreSmithSubnetFieldFaithful : FieldFaithful MooreSmithSubnetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := mooreSmithSubnetFields
  field_faithful := mooreSmithSubnet_fields_faithful

instance mooreSmithSubnetNontrivial : Nontrivial MooreSmithSubnetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MooreSmithSubnetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      MooreSmithSubnetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MooreSmithSubnetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  mooreSmithSubnetChapterTasteGate

theorem MooreSmithSubnetTasteGate_single_carrier_alignment :
    (∀ h : BHist, mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist h) = h) ∧
      (∀ x : MooreSmithSubnetUp,
        mooreSmithSubnetFromEventFlow (mooreSmithSubnetToEventFlow x) = some x) ∧
      (∀ x y : MooreSmithSubnetUp,
        mooreSmithSubnetToEventFlow x = mooreSmithSubnetToEventFlow y → x = y) ∧
      mooreSmithSubnetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  let decodeEncode :
      ∀ h : BHist, mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  let roundTrip :
      ∀ x : MooreSmithSubnetUp,
        mooreSmithSubnetFromEventFlow (mooreSmithSubnetToEventFlow x) = some x := by
    intro x
    cases x with
    | mk I J phi A T W D R E H C P N =>
        change
          some
            (MooreSmithSubnetUp.mk
              (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist I))
              (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist J))
              (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist phi))
              (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist A))
              (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist T))
              (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist W))
              (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist D))
              (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist R))
              (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist E))
              (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist H))
              (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist C))
              (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist P))
              (mooreSmithSubnetDecodeBHist (mooreSmithSubnetEncodeBHist N))) =
            some (MooreSmithSubnetUp.mk I J phi A T W D R E H C P N)
        let mkCongr
            {I' J' phi' A' T' W' D' R' E' H' C' P' N' : BHist}
            (hI : I' = I)
            (hJ : J' = J)
            (hPhi : phi' = phi)
            (hA : A' = A)
            (hT : T' = T)
            (hW : W' = W)
            (hD : D' = D)
            (hR : R' = R)
            (hE : E' = E)
            (hH : H' = H)
            (hC : C' = C)
            (hP : P' = P)
            (hN : N' = N) :
            MooreSmithSubnetUp.mk I' J' phi' A' T' W' D' R' E' H' C' P' N' =
              MooreSmithSubnetUp.mk I J phi A T W D R E H C P N := by
          cases hI
          cases hJ
          cases hPhi
          cases hA
          cases hT
          cases hW
          cases hD
          cases hR
          cases hE
          cases hH
          cases hC
          cases hP
          cases hN
          rfl
        exact
          congrArg some
            (mkCongr (decodeEncode I) (decodeEncode J) (decodeEncode phi)
              (decodeEncode A) (decodeEncode T) (decodeEncode W) (decodeEncode D)
              (decodeEncode R) (decodeEncode E) (decodeEncode H) (decodeEncode C)
              (decodeEncode P) (decodeEncode N))
  let toEventFlowInjective :
      ∀ x y : MooreSmithSubnetUp,
        mooreSmithSubnetToEventFlow x = mooreSmithSubnetToEventFlow y → x = y := by
    intro x y heq
    have hread :
        mooreSmithSubnetFromEventFlow (mooreSmithSubnetToEventFlow x) =
          mooreSmithSubnetFromEventFlow (mooreSmithSubnetToEventFlow y) :=
      congrArg mooreSmithSubnetFromEventFlow heq
    exact Option.some.inj (Eq.trans (roundTrip x).symm (Eq.trans hread (roundTrip y)))
  exact
    ⟨decodeEncode, roundTrip, fun x y heq => toEventFlowInjective x y heq, rfl⟩

end BEDC.Derived.MooreSmithSubnetUp
