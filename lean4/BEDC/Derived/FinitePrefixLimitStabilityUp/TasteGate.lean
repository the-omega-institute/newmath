import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FinitePrefixLimitStabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FinitePrefixLimitStabilityUp : Type where
  | packet (B W R D E H C P N : BHist) : FinitePrefixLimitStabilityUp
  deriving DecidableEq

def finitePrefixLimitStabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finitePrefixLimitStabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finitePrefixLimitStabilityEncodeBHist h

def finitePrefixLimitStabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finitePrefixLimitStabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finitePrefixLimitStabilityDecodeBHist tail)

private theorem FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      finitePrefixLimitStabilityDecodeBHist
        (finitePrefixLimitStabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_packet
    {B B' W W' R R' D D' E E' H H' C C' P P' N N' : BHist}
    (hB : B' = B) (hW : W' = W) (hR : R' = R) (hD : D' = D) (hE : E' = E)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    FinitePrefixLimitStabilityUp.packet B' W' R' D' E' H' C' P' N' =
      FinitePrefixLimitStabilityUp.packet B W R D E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hB
  cases hW
  cases hR
  cases hD
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private def FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_packetOfRaw
    (B W R D E H C P N : RawEvent) : FinitePrefixLimitStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  FinitePrefixLimitStabilityUp.packet
    (finitePrefixLimitStabilityDecodeBHist B)
    (finitePrefixLimitStabilityDecodeBHist W)
    (finitePrefixLimitStabilityDecodeBHist R)
    (finitePrefixLimitStabilityDecodeBHist D)
    (finitePrefixLimitStabilityDecodeBHist E)
    (finitePrefixLimitStabilityDecodeBHist H)
    (finitePrefixLimitStabilityDecodeBHist C)
    (finitePrefixLimitStabilityDecodeBHist P)
    (finitePrefixLimitStabilityDecodeBHist N)

def finitePrefixLimitStabilityToEventFlow : FinitePrefixLimitStabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FinitePrefixLimitStabilityUp.packet B W R D E H C P N =>
      [[BMark.b0],
        finitePrefixLimitStabilityEncodeBHist B,
        [BMark.b1, BMark.b0],
        finitePrefixLimitStabilityEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b0],
        finitePrefixLimitStabilityEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finitePrefixLimitStabilityEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finitePrefixLimitStabilityEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finitePrefixLimitStabilityEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finitePrefixLimitStabilityEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finitePrefixLimitStabilityEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finitePrefixLimitStabilityEncodeBHist N]

def finitePrefixLimitStabilityFromEventFlow :
    EventFlow → Option FinitePrefixLimitStabilityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      let packet := FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_packetOfRaw
      match rest0 with
      | [] => none
      | B :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | W :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | D :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | E :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | H :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | C :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | P :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | N :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (packet B W R D E H C P N)
                                                                          | _ :: _ =>
                                                                              none

private theorem FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FinitePrefixLimitStabilityUp,
      finitePrefixLimitStabilityFromEventFlow
        (finitePrefixLimitStabilityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | packet B W R D E H C P N =>
      change
        some
          (FinitePrefixLimitStabilityUp.packet
            (finitePrefixLimitStabilityDecodeBHist
              (finitePrefixLimitStabilityEncodeBHist B))
            (finitePrefixLimitStabilityDecodeBHist
              (finitePrefixLimitStabilityEncodeBHist W))
            (finitePrefixLimitStabilityDecodeBHist
              (finitePrefixLimitStabilityEncodeBHist R))
            (finitePrefixLimitStabilityDecodeBHist
              (finitePrefixLimitStabilityEncodeBHist D))
            (finitePrefixLimitStabilityDecodeBHist
              (finitePrefixLimitStabilityEncodeBHist E))
            (finitePrefixLimitStabilityDecodeBHist
              (finitePrefixLimitStabilityEncodeBHist H))
            (finitePrefixLimitStabilityDecodeBHist
              (finitePrefixLimitStabilityEncodeBHist C))
            (finitePrefixLimitStabilityDecodeBHist
              (finitePrefixLimitStabilityEncodeBHist P))
            (finitePrefixLimitStabilityDecodeBHist
              (finitePrefixLimitStabilityEncodeBHist N))) =
          some (FinitePrefixLimitStabilityUp.packet B W R D E H C P N)
      exact
        congrArg some
          (FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_packet
            (FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_decode B)
            (FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_decode W)
            (FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_decode R)
            (FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_decode D)
            (FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_decode E)
            (FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_decode H)
            (FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_decode C)
            (FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_decode P)
            (FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_decode N))

private theorem FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_injective
    {x y : FinitePrefixLimitStabilityUp} :
    finitePrefixLimitStabilityToEventFlow x = finitePrefixLimitStabilityToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finitePrefixLimitStabilityFromEventFlow
          (finitePrefixLimitStabilityToEventFlow x) =
        finitePrefixLimitStabilityFromEventFlow
          (finitePrefixLimitStabilityToEventFlow y) :=
    congrArg finitePrefixLimitStabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_round_trip y)))

instance finitePrefixLimitStabilityBHistCarrier :
    BHistCarrier FinitePrefixLimitStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finitePrefixLimitStabilityToEventFlow
  fromEventFlow := finitePrefixLimitStabilityFromEventFlow

instance finitePrefixLimitStabilityChapterTasteGate :
    ChapterTasteGate FinitePrefixLimitStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finitePrefixLimitStabilityFromEventFlow
        (finitePrefixLimitStabilityToEventFlow x) = some x
    exact FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_injective heq)

instance finitePrefixLimitStabilityFieldFaithful :
    FieldFaithful FinitePrefixLimitStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | FinitePrefixLimitStabilityUp.packet B W R D E H C P N => [B, W, R, D, E, H, C, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | packet B1 W1 R1 D1 E1 H1 C1 P1 N1 =>
        cases y with
        | packet B2 W2 R2 D2 E2 H2 C2 P2 N2 =>
            cases h
            rfl

instance finitePrefixLimitStabilityNontrivial :
    Nontrivial FinitePrefixLimitStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FinitePrefixLimitStabilityUp.packet BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FinitePrefixLimitStabilityUp.packet (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FinitePrefixLimitStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finitePrefixLimitStabilityChapterTasteGate

theorem FinitePrefixLimitStabilityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finitePrefixLimitStabilityDecodeBHist (finitePrefixLimitStabilityEncodeBHist h) = h) ∧
      (∀ x : FinitePrefixLimitStabilityUp,
        finitePrefixLimitStabilityFromEventFlow
            (finitePrefixLimitStabilityToEventFlow x) =
          some x) ∧
        (∀ x y : FinitePrefixLimitStabilityUp,
          finitePrefixLimitStabilityToEventFlow x =
              finitePrefixLimitStabilityToEventFlow y →
            x = y) ∧
          Nonempty (FieldFaithful FinitePrefixLimitStabilityUp) ∧
            Nonempty (ChapterTasteGate FinitePrefixLimitStabilityUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_decode
  · constructor
    · exact FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_injective heq
      · constructor
        · exact Nonempty.intro finitePrefixLimitStabilityFieldFaithful
        · exact Nonempty.intro finitePrefixLimitStabilityChapterTasteGate

theorem FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment :
    finitePrefixLimitStabilityEncodeBHist BHist.Empty = [] ∧
      (∀ h : BHist,
        finitePrefixLimitStabilityDecodeBHist
          (finitePrefixLimitStabilityEncodeBHist h) = h) ∧
      (∀ x : FinitePrefixLimitStabilityUp,
        finitePrefixLimitStabilityFromEventFlow
          (finitePrefixLimitStabilityToEventFlow x) = some x) ∧
      (∀ x y : FinitePrefixLimitStabilityUp,
        finitePrefixLimitStabilityToEventFlow x = finitePrefixLimitStabilityToEventFlow y →
          x = y) ∧
      Nonempty (ChapterTasteGate FinitePrefixLimitStabilityUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · exact FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_decode
    · constructor
      · exact FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_round_trip
      · constructor
        · intro x y hxy
          exact FinitePrefixLimitStabilityUpTasteGate_single_carrier_alignment_injective hxy
        · exact ⟨finitePrefixLimitStabilityChapterTasteGate⟩

theorem FinitePrefixLimitStabilityCarrier_admission [AskSetup] [PackageSetup]
    {B W R D E H C P N terminal : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    UnaryHistory B → UnaryHistory W → UnaryHistory D → UnaryHistory E →
      Cont B W R → Cont R D terminal → Cont terminal E C → hsame N E →
        PkgSig bundle terminal pkg →
          ∃ packet : FinitePrefixLimitStabilityUp,
            packet = FinitePrefixLimitStabilityUp.packet B W R D E H C P N ∧
              UnaryHistory B ∧ UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory D ∧
                UnaryHistory E ∧ UnaryHistory terminal ∧ Cont B W R ∧
                  Cont R D terminal ∧ Cont terminal E C ∧ hsame N E ∧
                    PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro unaryB unaryW unaryD unaryE contBW contRD contTerminalE sameName pkgTerminal
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryB unaryW contBW
  have unaryTerminal : UnaryHistory terminal :=
    unary_cont_closed unaryR unaryD contRD
  exact
    ⟨FinitePrefixLimitStabilityUp.packet B W R D E H C P N, rfl, unaryB, unaryW,
      unaryR, unaryD, unaryE, unaryTerminal, contBW, contRD, contTerminalE, sameName,
      pkgTerminal⟩

theorem FinitePrefixLimitStabilityCarrier_route_unary_closure
    {B W R D E H C P N BW WR RD DE : BHist}
    (hB : UnaryHistory B) (hW : UnaryHistory W) (hR : UnaryHistory R)
    (hD : UnaryHistory D) (hE : UnaryHistory E)
    (hBW : Cont B W BW) (hWR : Cont BW R WR) (hRD : Cont WR D RD)
    (hDE : Cont RD E DE) :
    FieldFaithful.fields (FinitePrefixLimitStabilityUp.packet B W R D E H C P N) =
        [B, W, R, D, E, H, C, P, N] ∧
      UnaryHistory BW ∧ UnaryHistory WR ∧ UnaryHistory RD ∧ UnaryHistory DE := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  have hBWUnary : UnaryHistory BW := unary_cont_closed hB hW hBW
  have hWRUnary : UnaryHistory WR := unary_cont_closed hBWUnary hR hWR
  have hRDUnary : UnaryHistory RD := unary_cont_closed hWRUnary hD hRD
  have hDEUnary : UnaryHistory DE := unary_cont_closed hRDUnary hE hDE
  constructor
  · rfl
  · constructor
    · exact hBWUnary
    · constructor
      · exact hWRUnary
      · constructor
        · exact hRDUnary
        · exact hDEUnary

theorem FinitePrefixLimitStabilityCarrier_real_seal_determinacy
    {B W R D E E' H C P N RD DE DE' : BHist}
    (hDE : Cont RD E DE) (hDE' : Cont RD E' DE') :
    FieldFaithful.fields (FinitePrefixLimitStabilityUp.packet B W R D E H C P N) =
        FieldFaithful.fields (FinitePrefixLimitStabilityUp.packet B W R D E' H C P N) →
      E = E' := by
  -- BEDC touchpoint anchor: BHist Cont FieldFaithful
  intro hfields
  cases hDE
  cases hDE'
  injection hfields with _ tailW
  injection tailW with _ tailR
  injection tailR with _ tailD
  injection tailD with _ tailE
  injection tailE with sealEq _

end BEDC.Derived.FinitePrefixLimitStabilityUp
