import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealIntervalUp : Type where
  | mk (L U rho Delta Lambda M Q H C P N : BHist) : LocatedRealIntervalUp
  deriving DecidableEq

def locatedRealIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealIntervalEncodeBHist h

def locatedRealIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealIntervalDecodeBHist tail)

private theorem LocatedRealIntervalTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem LocatedRealIntervalTasteGate_single_carrier_alignment_mk_congr
    {L1 U1 rho1 Delta1 Lambda1 M1 Q1 H1 C1 P1 N1 L2 U2 rho2 Delta2 Lambda2 M2 Q2 H2 C2 P2 N2 :
      BHist}
    (hL : L1 = L2)
    (hU : U1 = U2)
    (hrho : rho1 = rho2)
    (hDelta : Delta1 = Delta2)
    (hLambda : Lambda1 = Lambda2)
    (hM : M1 = M2)
    (hQ : Q1 = Q2)
    (hH : H1 = H2)
    (hC : C1 = C2)
    (hP : P1 = P2)
    (hN : N1 = N2) :
    LocatedRealIntervalUp.mk L1 U1 rho1 Delta1 Lambda1 M1 Q1 H1 C1 P1 N1 =
      LocatedRealIntervalUp.mk L2 U2 rho2 Delta2 Lambda2 M2 Q2 H2 C2 P2 N2 := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hL
  cases hU
  cases hrho
  cases hDelta
  cases hLambda
  cases hM
  cases hQ
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def locatedRealIntervalToEventFlow : LocatedRealIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealIntervalUp.mk L U rho Delta Lambda M Q H C P N =>
      [[BMark.b0],
        locatedRealIntervalEncodeBHist L,
        [BMark.b1, BMark.b0],
        locatedRealIntervalEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b0],
        locatedRealIntervalEncodeBHist rho,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedRealIntervalEncodeBHist Delta,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedRealIntervalEncodeBHist Lambda,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedRealIntervalEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedRealIntervalEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        locatedRealIntervalEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        locatedRealIntervalEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        locatedRealIntervalEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedRealIntervalEncodeBHist N]

def locatedRealIntervalPayloads : EventFlow → Option EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | [] => some []
  | _ :: rest =>
      match rest with
      | [] => none
      | row :: tail =>
          match locatedRealIntervalPayloads tail with
          | some rows => some (row :: rows)
          | none => none

def locatedRealIntervalFromPayloads : EventFlow → Option LocatedRealIntervalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | L :: restU =>
      match restU with
      | [] => none
      | U :: restrho =>
          match restrho with
          | [] => none
          | rho :: restDelta =>
              match restDelta with
              | [] => none
              | Delta :: restLambda =>
                  match restLambda with
                  | [] => none
                  | Lambda :: restM =>
                      match restM with
                      | [] => none
                      | M :: restQ =>
                          match restQ with
                          | [] => none
                          | Q :: restH =>
                              match restH with
                              | [] => none
                              | H :: restC =>
                                  match restC with
                                  | [] => none
                                  | C :: restP =>
                                      match restP with
                                      | [] => none
                                      | P :: restN =>
                                          match restN with
                                          | [] => none
                                          | N :: rest =>
                                              match rest with
                                              | [] =>
                                                  some (LocatedRealIntervalUp.mk
                                                    (locatedRealIntervalDecodeBHist L)
                                                    (locatedRealIntervalDecodeBHist U)
                                                    (locatedRealIntervalDecodeBHist rho)
                                                    (locatedRealIntervalDecodeBHist Delta)
                                                    (locatedRealIntervalDecodeBHist Lambda)
                                                    (locatedRealIntervalDecodeBHist M)
                                                    (locatedRealIntervalDecodeBHist Q)
                                                    (locatedRealIntervalDecodeBHist H)
                                                    (locatedRealIntervalDecodeBHist C)
                                                    (locatedRealIntervalDecodeBHist P)
                                                    (locatedRealIntervalDecodeBHist N))
                                              | _ :: _ => none

def locatedRealIntervalFromEventFlow
    (flow : EventFlow) : Option LocatedRealIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match locatedRealIntervalPayloads flow with
  | some rows => locatedRealIntervalFromPayloads rows
  | none => none

private theorem LocatedRealIntervalTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedRealIntervalUp,
      locatedRealIntervalFromEventFlow (locatedRealIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U rho Delta Lambda M Q H C P N =>
      change
        some
          (LocatedRealIntervalUp.mk
            (locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist L))
            (locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist U))
            (locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist rho))
            (locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist Delta))
            (locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist Lambda))
            (locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist M))
            (locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist Q))
            (locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist H))
            (locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist C))
            (locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist P))
            (locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist N))) =
          some (LocatedRealIntervalUp.mk L U rho Delta Lambda M Q H C P N)
      exact congrArg some
        (LocatedRealIntervalTasteGate_single_carrier_alignment_mk_congr
          (LocatedRealIntervalTasteGate_single_carrier_alignment_decode L)
          (LocatedRealIntervalTasteGate_single_carrier_alignment_decode U)
          (LocatedRealIntervalTasteGate_single_carrier_alignment_decode rho)
          (LocatedRealIntervalTasteGate_single_carrier_alignment_decode Delta)
          (LocatedRealIntervalTasteGate_single_carrier_alignment_decode Lambda)
          (LocatedRealIntervalTasteGate_single_carrier_alignment_decode M)
          (LocatedRealIntervalTasteGate_single_carrier_alignment_decode Q)
          (LocatedRealIntervalTasteGate_single_carrier_alignment_decode H)
          (LocatedRealIntervalTasteGate_single_carrier_alignment_decode C)
          (LocatedRealIntervalTasteGate_single_carrier_alignment_decode P)
          (LocatedRealIntervalTasteGate_single_carrier_alignment_decode N))

private theorem LocatedRealIntervalTasteGate_single_carrier_alignment_injective
    {x y : LocatedRealIntervalUp} :
    locatedRealIntervalToEventFlow x = locatedRealIntervalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRealIntervalFromEventFlow (locatedRealIntervalToEventFlow x) =
        locatedRealIntervalFromEventFlow (locatedRealIntervalToEventFlow y) :=
    congrArg locatedRealIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedRealIntervalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedRealIntervalTasteGate_single_carrier_alignment_round_trip y)))

instance locatedRealIntervalBHistCarrier : BHistCarrier LocatedRealIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRealIntervalToEventFlow
  fromEventFlow := locatedRealIntervalFromEventFlow

instance locatedRealIntervalChapterTasteGate : ChapterTasteGate LocatedRealIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedRealIntervalFromEventFlow (locatedRealIntervalToEventFlow x) = some x
    exact LocatedRealIntervalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedRealIntervalTasteGate_single_carrier_alignment_injective heq)

theorem LocatedRealIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist h) = h) ∧
      (∀ x : LocatedRealIntervalUp,
        locatedRealIntervalFromEventFlow (locatedRealIntervalToEventFlow x) = some x) ∧
      (∀ x y : LocatedRealIntervalUp,
        locatedRealIntervalToEventFlow x = locatedRealIntervalToEventFlow y → x = y) ∧
      locatedRealIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    And.intro LocatedRealIntervalTasteGate_single_carrier_alignment_decode
      (And.intro LocatedRealIntervalTasteGate_single_carrier_alignment_round_trip
        (And.intro
          (fun x y heq => LocatedRealIntervalTasteGate_single_carrier_alignment_injective heq)
          rfl))

end BEDC.Derived.LocatedRealIntervalUp
