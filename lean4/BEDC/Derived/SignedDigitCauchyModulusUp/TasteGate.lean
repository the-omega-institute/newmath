import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SignedDigitCauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SignedDigitCauchyModulusUp : Type where
  | mk (S W E T R L H C P N : BHist) : SignedDigitCauchyModulusUp
  deriving DecidableEq

def signedDigitCauchyModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: signedDigitCauchyModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: signedDigitCauchyModulusEncodeBHist h

def signedDigitCauchyModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (signedDigitCauchyModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (signedDigitCauchyModulusDecodeBHist tail)

private theorem SignedDigitCauchyModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      signedDigitCauchyModulusDecodeBHist (signedDigitCauchyModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def signedDigitCauchyModulusFields : SignedDigitCauchyModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SignedDigitCauchyModulusUp.mk S W E T R L H C P N => [S, W, E, T, R, L, H, C, P, N]

def signedDigitCauchyModulusToEventFlow : SignedDigitCauchyModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (signedDigitCauchyModulusFields x).map signedDigitCauchyModulusEncodeBHist

private def signedDigitCauchyModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => signedDigitCauchyModulusEventAtDefault index rest

def signedDigitCauchyModulusFromEventFlow
    (ef : EventFlow) : Option SignedDigitCauchyModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SignedDigitCauchyModulusUp.mk
      (signedDigitCauchyModulusDecodeBHist (signedDigitCauchyModulusEventAtDefault 0 ef))
      (signedDigitCauchyModulusDecodeBHist (signedDigitCauchyModulusEventAtDefault 1 ef))
      (signedDigitCauchyModulusDecodeBHist (signedDigitCauchyModulusEventAtDefault 2 ef))
      (signedDigitCauchyModulusDecodeBHist (signedDigitCauchyModulusEventAtDefault 3 ef))
      (signedDigitCauchyModulusDecodeBHist (signedDigitCauchyModulusEventAtDefault 4 ef))
      (signedDigitCauchyModulusDecodeBHist (signedDigitCauchyModulusEventAtDefault 5 ef))
      (signedDigitCauchyModulusDecodeBHist (signedDigitCauchyModulusEventAtDefault 6 ef))
      (signedDigitCauchyModulusDecodeBHist (signedDigitCauchyModulusEventAtDefault 7 ef))
      (signedDigitCauchyModulusDecodeBHist (signedDigitCauchyModulusEventAtDefault 8 ef))
      (signedDigitCauchyModulusDecodeBHist (signedDigitCauchyModulusEventAtDefault 9 ef)))

private theorem SignedDigitCauchyModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SignedDigitCauchyModulusUp,
      signedDigitCauchyModulusFromEventFlow (signedDigitCauchyModulusToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk S W E T R L H C P N =>
      change
        some
          (SignedDigitCauchyModulusUp.mk
            (signedDigitCauchyModulusDecodeBHist (signedDigitCauchyModulusEncodeBHist S))
            (signedDigitCauchyModulusDecodeBHist (signedDigitCauchyModulusEncodeBHist W))
            (signedDigitCauchyModulusDecodeBHist (signedDigitCauchyModulusEncodeBHist E))
            (signedDigitCauchyModulusDecodeBHist (signedDigitCauchyModulusEncodeBHist T))
            (signedDigitCauchyModulusDecodeBHist (signedDigitCauchyModulusEncodeBHist R))
            (signedDigitCauchyModulusDecodeBHist (signedDigitCauchyModulusEncodeBHist L))
            (signedDigitCauchyModulusDecodeBHist (signedDigitCauchyModulusEncodeBHist H))
            (signedDigitCauchyModulusDecodeBHist (signedDigitCauchyModulusEncodeBHist C))
            (signedDigitCauchyModulusDecodeBHist (signedDigitCauchyModulusEncodeBHist P))
            (signedDigitCauchyModulusDecodeBHist (signedDigitCauchyModulusEncodeBHist N))) =
          some (SignedDigitCauchyModulusUp.mk S W E T R L H C P N)
      rw [SignedDigitCauchyModulusTasteGate_single_carrier_alignment_decode S,
        SignedDigitCauchyModulusTasteGate_single_carrier_alignment_decode W,
        SignedDigitCauchyModulusTasteGate_single_carrier_alignment_decode E,
        SignedDigitCauchyModulusTasteGate_single_carrier_alignment_decode T,
        SignedDigitCauchyModulusTasteGate_single_carrier_alignment_decode R,
        SignedDigitCauchyModulusTasteGate_single_carrier_alignment_decode L,
        SignedDigitCauchyModulusTasteGate_single_carrier_alignment_decode H,
        SignedDigitCauchyModulusTasteGate_single_carrier_alignment_decode C,
        SignedDigitCauchyModulusTasteGate_single_carrier_alignment_decode P,
        SignedDigitCauchyModulusTasteGate_single_carrier_alignment_decode N]

private theorem SignedDigitCauchyModulusTasteGate_single_carrier_alignment_injective
    {x y : SignedDigitCauchyModulusUp} :
    signedDigitCauchyModulusToEventFlow x = signedDigitCauchyModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      signedDigitCauchyModulusFromEventFlow (signedDigitCauchyModulusToEventFlow x) =
        signedDigitCauchyModulusFromEventFlow (signedDigitCauchyModulusToEventFlow y) :=
    congrArg signedDigitCauchyModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SignedDigitCauchyModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SignedDigitCauchyModulusTasteGate_single_carrier_alignment_round_trip y)))

instance signedDigitCauchyModulusBHistCarrier : BHistCarrier SignedDigitCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := signedDigitCauchyModulusToEventFlow
  fromEventFlow := signedDigitCauchyModulusFromEventFlow

instance signedDigitCauchyModulusChapterTasteGate :
    ChapterTasteGate SignedDigitCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change signedDigitCauchyModulusFromEventFlow (signedDigitCauchyModulusToEventFlow x) =
      some x
    exact SignedDigitCauchyModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SignedDigitCauchyModulusTasteGate_single_carrier_alignment_injective heq)

def SignedDigitCauchyModulusCarrier [AskSetup] [PackageSetup]
    (S W E T R L H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory E ∧ UnaryHistory T ∧
    UnaryHistory R ∧ UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory C ∧
      PkgSig bundle P pkg ∧ UnaryHistory N

theorem SignedDigitCauchyModulusNameCertObligations [AskSetup] [PackageSetup]
    {S W E T R L H C P N normalized thresholdRead regularRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedDigitCauchyModulusCarrier S W E T R L H C P N bundle pkg ->
      Cont S W normalized ->
        Cont normalized E thresholdRead ->
          Cont thresholdRead T regularRead ->
            Cont regularRead L sealRead ->
              PkgSig bundle sealRead pkg ->
                UnaryHistory normalized ∧ UnaryHistory thresholdRead ∧
                  UnaryHistory regularRead ∧ UnaryHistory sealRead ∧ Cont S W normalized ∧
                    Cont normalized E thresholdRead ∧ Cont thresholdRead T regularRead ∧
                      Cont regularRead L sealRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier sourceWindowNormalized normalizedEndpointThreshold thresholdRegularRead
    regularSealRead sealPkg
  obtain ⟨sourceUnary, windowUnary, endpointUnary, thresholdUnary, _regularUnary, sealUnary,
    _transportUnary, _routeUnary, provenancePkg, _nameUnary⟩ := carrier
  have normalizedUnary : UnaryHistory normalized :=
    unary_cont_closed sourceUnary windowUnary sourceWindowNormalized
  have thresholdReadUnary : UnaryHistory thresholdRead :=
    unary_cont_closed normalizedUnary endpointUnary normalizedEndpointThreshold
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed thresholdReadUnary thresholdUnary thresholdRegularRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regularReadUnary sealUnary regularSealRead
  exact
    ⟨normalizedUnary, thresholdReadUnary, regularReadUnary, sealReadUnary,
      sourceWindowNormalized, normalizedEndpointThreshold, thresholdRegularRead, regularSealRead,
      provenancePkg, sealPkg⟩

theorem SignedDigitCauchyModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      signedDigitCauchyModulusDecodeBHist (signedDigitCauchyModulusEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SignedDigitCauchyModulusUp) ∧
        Nonempty (ChapterTasteGate SignedDigitCauchyModulusUp) ∧
          signedDigitCauchyModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨SignedDigitCauchyModulusTasteGate_single_carrier_alignment_decode,
      Nonempty.intro signedDigitCauchyModulusBHistCarrier,
      Nonempty.intro signedDigitCauchyModulusChapterTasteGate,
      rfl⟩

end BEDC.Derived.SignedDigitCauchyModulusUp
