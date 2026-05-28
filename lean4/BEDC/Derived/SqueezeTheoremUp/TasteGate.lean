import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SqueezeTheoremUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SqueezeTheoremUp : Type where
  | mk (lower middle upper window dyadic readback realSeal transport replay provenance
      localCert endpoint : BHist) : SqueezeTheoremUp
  deriving DecidableEq

private def squeezeTheoremEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: squeezeTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: squeezeTheoremEncodeBHist h

private def squeezeTheoremDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (squeezeTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (squeezeTheoremDecodeBHist tail)

private theorem squeezeTheorem_decode_encode_bhist :
    forall h : BHist, squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def squeezeTheoremEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => squeezeTheoremEventAt index rest

private def squeezeTheoremFields : SqueezeTheoremUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SqueezeTheoremUp.mk lower middle upper window dyadic readback realSeal transport replay
      provenance localCert endpoint =>
      [lower, middle, upper, window, dyadic, readback, realSeal, transport, replay,
        provenance, localCert, endpoint]

private def squeezeTheoremToEventFlow : SqueezeTheoremUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun token => (squeezeTheoremFields token).map squeezeTheoremEncodeBHist

private def squeezeTheoremFromEventFlow (flow : EventFlow) : Option SqueezeTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SqueezeTheoremUp.mk
      (squeezeTheoremDecodeBHist (squeezeTheoremEventAt 0 flow))
      (squeezeTheoremDecodeBHist (squeezeTheoremEventAt 1 flow))
      (squeezeTheoremDecodeBHist (squeezeTheoremEventAt 2 flow))
      (squeezeTheoremDecodeBHist (squeezeTheoremEventAt 3 flow))
      (squeezeTheoremDecodeBHist (squeezeTheoremEventAt 4 flow))
      (squeezeTheoremDecodeBHist (squeezeTheoremEventAt 5 flow))
      (squeezeTheoremDecodeBHist (squeezeTheoremEventAt 6 flow))
      (squeezeTheoremDecodeBHist (squeezeTheoremEventAt 7 flow))
      (squeezeTheoremDecodeBHist (squeezeTheoremEventAt 8 flow))
      (squeezeTheoremDecodeBHist (squeezeTheoremEventAt 9 flow))
      (squeezeTheoremDecodeBHist (squeezeTheoremEventAt 10 flow))
      (squeezeTheoremDecodeBHist (squeezeTheoremEventAt 11 flow)))

private theorem squeezeTheorem_round_trip :
    forall x : SqueezeTheoremUp,
      squeezeTheoremFromEventFlow (squeezeTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk lower middle upper window dyadic readback realSeal transport replay provenance
      localCert endpoint =>
      change
        some
          (SqueezeTheoremUp.mk
            (squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist lower))
            (squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist middle))
            (squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist upper))
            (squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist window))
            (squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist dyadic))
            (squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist readback))
            (squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist realSeal))
            (squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist transport))
            (squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist replay))
            (squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist provenance))
            (squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist localCert))
            (squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist endpoint))) =
          some
            (SqueezeTheoremUp.mk lower middle upper window dyadic readback realSeal
              transport replay provenance localCert endpoint)
      rw [squeezeTheorem_decode_encode_bhist lower,
        squeezeTheorem_decode_encode_bhist middle,
        squeezeTheorem_decode_encode_bhist upper,
        squeezeTheorem_decode_encode_bhist window,
        squeezeTheorem_decode_encode_bhist dyadic,
        squeezeTheorem_decode_encode_bhist readback,
        squeezeTheorem_decode_encode_bhist realSeal,
        squeezeTheorem_decode_encode_bhist transport,
        squeezeTheorem_decode_encode_bhist replay,
        squeezeTheorem_decode_encode_bhist provenance,
        squeezeTheorem_decode_encode_bhist localCert,
        squeezeTheorem_decode_encode_bhist endpoint]

private theorem squeezeTheoremToEventFlow_injective {x y : SqueezeTheoremUp} :
    squeezeTheoremToEventFlow x = squeezeTheoremToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      squeezeTheoremFromEventFlow (squeezeTheoremToEventFlow x) =
        squeezeTheoremFromEventFlow (squeezeTheoremToEventFlow y) :=
    congrArg squeezeTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (squeezeTheorem_round_trip x).symm
      (Eq.trans hread (squeezeTheorem_round_trip y)))

instance squeezeTheoremBHistCarrier : BHistCarrier SqueezeTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := squeezeTheoremToEventFlow
  fromEventFlow := squeezeTheoremFromEventFlow

instance squeezeTheoremChapterTasteGate : ChapterTasteGate SqueezeTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change squeezeTheoremFromEventFlow (squeezeTheoremToEventFlow x) = some x
    exact squeezeTheorem_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (squeezeTheoremToEventFlow_injective heq)

def taste_gate : ChapterTasteGate SqueezeTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  squeezeTheoremChapterTasteGate

def SqueezeTheoremCarrier [AskSetup] [PackageSetup]
    (lower middle upper window dyadic readback realSeal transport replay provenance localCert
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory lower ∧ UnaryHistory middle ∧ UnaryHistory upper ∧
    UnaryHistory window ∧ UnaryHistory dyadic ∧ UnaryHistory readback ∧
      UnaryHistory realSeal ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localCert ∧ UnaryHistory endpoint ∧
          Cont lower middle window ∧ Cont window dyadic readback ∧
            Cont readback realSeal endpoint ∧ Cont transport replay provenance ∧
              PkgSig bundle endpoint pkg

theorem SqueezeTheoremCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {lower middle upper window dyadic readback realSeal transport replay provenance localCert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SqueezeTheoremCarrier lower middle upper window dyadic readback realSeal transport replay
        provenance localCert endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            SqueezeTheoremCarrier lower middle upper window dyadic readback realSeal transport
              replay provenance localCert endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ Cont window dyadic readback)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          hsame ∧
        UnaryHistory lower ∧ UnaryHistory middle ∧ UnaryHistory upper ∧ UnaryHistory window ∧
          UnaryHistory dyadic ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
            Cont lower middle window ∧ Cont window dyadic readback ∧
              Cont readback realSeal endpoint ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory SemanticNameCert
  intro carrier
  have carrierWitness := carrier
  rcases carrier with
    ⟨lowerUnary, middleUnary, upperUnary, windowUnary, dyadicUnary, readbackUnary,
      realSealUnary, _transportUnary, _replayUnary, _provenanceUnary, _localCertUnary,
      _endpointUnary, lowerMiddleWindow, windowDyadicReadback, readbackRealSealEndpoint,
      _transportReplayProvenance, endpointPkg⟩
  have sourceEndpoint :
      (fun row : BHist =>
        SqueezeTheoremCarrier lower middle upper window dyadic readback realSeal transport
          replay provenance localCert endpoint bundle pkg ∧ hsame row endpoint) endpoint := by
    exact ⟨carrierWitness, hsame_refl endpoint⟩
  have core :
      NameCert
        (fun row : BHist =>
          SqueezeTheoremCarrier lower middle upper window dyadic readback realSeal transport
            replay provenance localCert endpoint bundle pkg ∧ hsame row endpoint)
        hsame := {
    carrier_inhabited := Exists.intro endpoint sourceEndpoint
    equiv_refl := by
      intro row _source
      exact hsame_refl row
    equiv_symm := by
      intro _row _row' sameRows
      exact hsame_symm sameRows
    equiv_trans := by
      intro _row _row' _row'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    carrier_respects_equiv := by
      intro _row _row' sameRows source
      exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
  }
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            SqueezeTheoremCarrier lower middle upper window dyadic readback realSeal transport
              replay provenance localCert endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ Cont window dyadic readback)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := core
    pattern_sound := by
      intro _row source
      exact ⟨source.right, windowDyadicReadback⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right, endpointPkg⟩
  }
  exact
    ⟨cert, lowerUnary, middleUnary, upperUnary, windowUnary, dyadicUnary, readbackUnary,
      realSealUnary, lowerMiddleWindow, windowDyadicReadback, readbackRealSealEndpoint,
      endpointPkg⟩

end BEDC.Derived.SqueezeTheoremUp
