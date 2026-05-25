import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyAdditionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyAdditionUp : Type where
  | mk (R0 R1 W0 W1 T0 T1 D S E Z H C P N : BHist) : RegularCauchyAdditionUp
  deriving DecidableEq

def regularCauchyAdditionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyAdditionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyAdditionEncodeBHist h

def regularCauchyAdditionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyAdditionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyAdditionDecodeBHist tail)

private theorem RegularCauchyAdditionUp_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyAdditionFields : RegularCauchyAdditionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyAdditionUp.mk R0 R1 W0 W1 T0 T1 D S E Z H C P N =>
      [R0, R1, W0, W1, T0, T1, D, S, E, Z, H, C, P, N]

def regularCauchyAdditionToEventFlow : RegularCauchyAdditionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyAdditionFields x).map regularCauchyAdditionEncodeBHist

def regularCauchyAdditionFromEventFlow : EventFlow → Option RegularCauchyAdditionUp
  -- BEDC touchpoint anchor: BHist BMark
  | R0 :: restR0 =>
      match restR0 with
      | R1 :: restR1 =>
          match restR1 with
          | W0 :: restW0 =>
              match restW0 with
              | W1 :: restW1 =>
                  match restW1 with
                  | T0 :: restT0 =>
                      match restT0 with
                      | T1 :: restT1 =>
                          match restT1 with
                          | D :: restD =>
                              match restD with
                              | S :: restS =>
                                  match restS with
                                  | E :: restE =>
                                      match restE with
                                      | Z :: restZ =>
                                          match restZ with
                                          | H :: restH =>
                                              match restH with
                                              | C :: restC =>
                                                  match restC with
                                                  | P :: restP =>
                                                      match restP with
                                                      | N :: restN =>
                                                          match restN with
                                                          | [] =>
                                                              some
                                                                (RegularCauchyAdditionUp.mk
                                                                  (regularCauchyAdditionDecodeBHist R0)
                                                                  (regularCauchyAdditionDecodeBHist R1)
                                                                  (regularCauchyAdditionDecodeBHist W0)
                                                                  (regularCauchyAdditionDecodeBHist W1)
                                                                  (regularCauchyAdditionDecodeBHist T0)
                                                                  (regularCauchyAdditionDecodeBHist T1)
                                                                  (regularCauchyAdditionDecodeBHist D)
                                                                  (regularCauchyAdditionDecodeBHist S)
                                                                  (regularCauchyAdditionDecodeBHist E)
                                                                  (regularCauchyAdditionDecodeBHist Z)
                                                                  (regularCauchyAdditionDecodeBHist H)
                                                                  (regularCauchyAdditionDecodeBHist C)
                                                                  (regularCauchyAdditionDecodeBHist P)
                                                                  (regularCauchyAdditionDecodeBHist N))
                                                          | _ :: _ => none
                                                      | [] => none
                                                  | [] => none
                                              | [] => none
                                          | [] => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem regularCauchyAddition_mk_congr
    {R0 R0' R1 R1' W0 W0' W1 W1' T0 T0' T1 T1' D D' S S' E E' Z Z'
      H H' C C' P P' N N' : BHist}
    (hR0 : R0' = R0) (hR1 : R1' = R1) (hW0 : W0' = W0) (hW1 : W1' = W1)
    (hT0 : T0' = T0) (hT1 : T1' = T1) (hD : D' = D) (hS : S' = S)
    (hE : E' = E) (hZ : Z' = Z) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    RegularCauchyAdditionUp.mk R0' R1' W0' W1' T0' T1' D' S' E' Z' H' C' P' N' =
      RegularCauchyAdditionUp.mk R0 R1 W0 W1 T0 T1 D S E Z H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hR0
  cases hR1
  cases hW0
  cases hW1
  cases hT0
  cases hT1
  cases hD
  cases hS
  cases hE
  cases hZ
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem RegularCauchyAdditionUp_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyAdditionUp,
      regularCauchyAdditionFromEventFlow (regularCauchyAdditionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R0 R1 W0 W1 T0 T1 D S E Z H C P N =>
      exact congrArg some
        (regularCauchyAddition_mk_congr
          (RegularCauchyAdditionUp_single_carrier_alignment_decode R0)
          (RegularCauchyAdditionUp_single_carrier_alignment_decode R1)
          (RegularCauchyAdditionUp_single_carrier_alignment_decode W0)
          (RegularCauchyAdditionUp_single_carrier_alignment_decode W1)
          (RegularCauchyAdditionUp_single_carrier_alignment_decode T0)
          (RegularCauchyAdditionUp_single_carrier_alignment_decode T1)
          (RegularCauchyAdditionUp_single_carrier_alignment_decode D)
          (RegularCauchyAdditionUp_single_carrier_alignment_decode S)
          (RegularCauchyAdditionUp_single_carrier_alignment_decode E)
          (RegularCauchyAdditionUp_single_carrier_alignment_decode Z)
          (RegularCauchyAdditionUp_single_carrier_alignment_decode H)
          (RegularCauchyAdditionUp_single_carrier_alignment_decode C)
          (RegularCauchyAdditionUp_single_carrier_alignment_decode P)
          (RegularCauchyAdditionUp_single_carrier_alignment_decode N))

private theorem regularCauchyAdditionToEventFlow_injective
    {x y : RegularCauchyAdditionUp} :
    regularCauchyAdditionToEventFlow x = regularCauchyAdditionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyAdditionFromEventFlow (regularCauchyAdditionToEventFlow x) =
        regularCauchyAdditionFromEventFlow (regularCauchyAdditionToEventFlow y) :=
    congrArg regularCauchyAdditionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchyAdditionUp_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegularCauchyAdditionUp_single_carrier_alignment_round_trip y)))

instance regularCauchyAdditionBHistCarrier :
    BHistCarrier RegularCauchyAdditionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyAdditionToEventFlow
  fromEventFlow := regularCauchyAdditionFromEventFlow

instance regularCauchyAdditionChapterTasteGate :
    ChapterTasteGate RegularCauchyAdditionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyAdditionFromEventFlow (regularCauchyAdditionToEventFlow x) = some x
    exact RegularCauchyAdditionUp_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyAdditionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyAdditionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyAdditionChapterTasteGate

theorem RegularCauchyAdditionUp_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyAdditionUp,
        regularCauchyAdditionFromEventFlow (regularCauchyAdditionToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchyAdditionUp,
        regularCauchyAdditionToEventFlow x = regularCauchyAdditionToEventFlow y →
          x = y) ∧
      regularCauchyAdditionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RegularCauchyAdditionUp_single_carrier_alignment_decode
  constructor
  · exact RegularCauchyAdditionUp_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact regularCauchyAdditionToEventFlow_injective heq
  · rfl

theorem RegularCauchyAdditionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyAdditionUp,
        regularCauchyAdditionFromEventFlow (regularCauchyAdditionToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchyAdditionUp,
        regularCauchyAdditionToEventFlow x = regularCauchyAdditionToEventFlow y →
          x = y) ∧
      regularCauchyAdditionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact RegularCauchyAdditionUp_single_carrier_alignment

def RegularCauchyAdditionCarrier [AskSetup] [PackageSetup]
    (R0 R1 W0 W1 T0 T1 D S E Z H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory R0 ∧ UnaryHistory R1 ∧ UnaryHistory W0 ∧ UnaryHistory W1 ∧
    UnaryHistory T0 ∧ UnaryHistory T1 ∧ UnaryHistory D ∧ UnaryHistory S ∧
      UnaryHistory E ∧ UnaryHistory Z ∧ UnaryHistory H ∧ UnaryHistory C ∧
        UnaryHistory P ∧ UnaryHistory N ∧ Cont R0 R1 W0 ∧ Cont W0 W1 T0 ∧
          Cont T0 T1 D ∧ Cont D E H ∧ Cont H C S ∧ Cont S Z P ∧
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem RegularCauchyAdditionCarrier_real_seal_handoff [AskSetup] [PackageSetup]
    {R0 R1 W0 W1 T0 T1 D S E Z H C P N sourceRead endpointRead ledgerRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyAdditionCarrier R0 R1 W0 W1 T0 T1 D S E Z H C P N bundle pkg →
      Cont R0 R1 sourceRead →
        Cont T0 T1 endpointRead →
          Cont D E ledgerRead →
            Cont S Z sealRead →
              PkgSig bundle sealRead pkg →
                UnaryHistory R0 ∧ UnaryHistory R1 ∧ UnaryHistory T0 ∧
                  UnaryHistory T1 ∧ UnaryHistory D ∧ UnaryHistory E ∧
                    UnaryHistory S ∧ UnaryHistory Z ∧ UnaryHistory sealRead ∧
                      Cont R0 R1 sourceRead ∧ Cont T0 T1 endpointRead ∧
                        Cont D E ledgerRead ∧ Cont S Z sealRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier sourceRoute endpointRoute ledgerRoute sealRoute sealSig
  obtain ⟨R0Unary, R1Unary, _W0Unary, _W1Unary, T0Unary, T1Unary, DUnary, SUnary,
    EUnary, ZUnary, _HUnary, _CUnary, _PUnary, _NUnary, _R0R1W0, _W0W1T0,
    _T0T1D, _DEH, _HCS, _SZP, provenanceSig, _nameSig⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed SUnary ZUnary sealRoute
  exact
    ⟨R0Unary, R1Unary, T0Unary, T1Unary, DUnary, EUnary, SUnary, ZUnary,
      sealReadUnary, sourceRoute, endpointRoute, ledgerRoute, sealRoute,
      provenanceSig, sealSig⟩

end BEDC.Derived.RegularCauchyAdditionUp
