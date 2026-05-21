import BEDC.Derived.ValidatedNumericsUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ValidatedNumericsUp

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

inductive ValidatedNumericsUp : Type where
  | mk (interval precision modulus observation readback transport containment provenance name :
      BHist) : ValidatedNumericsUp
  deriving DecidableEq

def validatedNumericsEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: validatedNumericsEncodeBHist h
  | BHist.e1 h => BMark.b1 :: validatedNumericsEncodeBHist h

def validatedNumericsDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (validatedNumericsDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (validatedNumericsDecodeBHist tail)

private def validatedNumericsNthRawEvent : EventFlow → Nat → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | [], _ => []
  | head :: _tail, Nat.zero => head
  | _head :: tail, Nat.succ n => validatedNumericsNthRawEvent tail n

private theorem validatedNumerics_decode_encode_bhist :
    ∀ h : BHist, validatedNumericsDecodeBHist (validatedNumericsEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem validatedNumerics_mk_congr
    {interval interval' precision precision' modulus modulus' observation observation'
      readback readback' transport transport' containment containment' provenance provenance'
      name name' : BHist}
    (hInterval : interval' = interval)
    (hPrecision : precision' = precision)
    (hModulus : modulus' = modulus)
    (hObservation : observation' = observation)
    (hReadback : readback' = readback)
    (hTransport : transport' = transport)
    (hContainment : containment' = containment)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    ValidatedNumericsUp.mk interval' precision' modulus' observation' readback' transport'
        containment' provenance' name' =
      ValidatedNumericsUp.mk interval precision modulus observation readback transport
        containment provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hInterval
  cases hPrecision
  cases hModulus
  cases hObservation
  cases hReadback
  cases hTransport
  cases hContainment
  cases hProvenance
  cases hName
  rfl

def validatedNumericsToEventFlow : ValidatedNumericsUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ValidatedNumericsUp.mk interval precision modulus observation readback transport containment
      provenance name =>
      [validatedNumericsEncodeBHist interval,
        validatedNumericsEncodeBHist precision,
        validatedNumericsEncodeBHist modulus,
        validatedNumericsEncodeBHist observation,
        validatedNumericsEncodeBHist readback,
        validatedNumericsEncodeBHist transport,
        validatedNumericsEncodeBHist containment,
        validatedNumericsEncodeBHist provenance,
        validatedNumericsEncodeBHist name]

def validatedNumericsFromEventFlow (ef : EventFlow) : Option ValidatedNumericsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ValidatedNumericsUp.mk
      (validatedNumericsDecodeBHist (validatedNumericsNthRawEvent ef 0))
      (validatedNumericsDecodeBHist (validatedNumericsNthRawEvent ef 1))
      (validatedNumericsDecodeBHist (validatedNumericsNthRawEvent ef 2))
      (validatedNumericsDecodeBHist (validatedNumericsNthRawEvent ef 3))
      (validatedNumericsDecodeBHist (validatedNumericsNthRawEvent ef 4))
      (validatedNumericsDecodeBHist (validatedNumericsNthRawEvent ef 5))
      (validatedNumericsDecodeBHist (validatedNumericsNthRawEvent ef 6))
      (validatedNumericsDecodeBHist (validatedNumericsNthRawEvent ef 7))
      (validatedNumericsDecodeBHist (validatedNumericsNthRawEvent ef 8)))

private theorem validatedNumerics_round_trip :
    ∀ x : ValidatedNumericsUp,
      validatedNumericsFromEventFlow (validatedNumericsToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk interval precision modulus observation readback transport containment provenance name =>
      exact
        congrArg some
          (validatedNumerics_mk_congr
            (validatedNumerics_decode_encode_bhist interval)
            (validatedNumerics_decode_encode_bhist precision)
            (validatedNumerics_decode_encode_bhist modulus)
            (validatedNumerics_decode_encode_bhist observation)
            (validatedNumerics_decode_encode_bhist readback)
            (validatedNumerics_decode_encode_bhist transport)
            (validatedNumerics_decode_encode_bhist containment)
            (validatedNumerics_decode_encode_bhist provenance)
            (validatedNumerics_decode_encode_bhist name))

private theorem validatedNumericsToEventFlow_injective {x y : ValidatedNumericsUp} :
    validatedNumericsToEventFlow x = validatedNumericsToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      validatedNumericsFromEventFlow (validatedNumericsToEventFlow x) =
        validatedNumericsFromEventFlow (validatedNumericsToEventFlow y) :=
    congrArg validatedNumericsFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (validatedNumerics_round_trip x).symm
      (Eq.trans hread (validatedNumerics_round_trip y)))

instance validatedNumericsBHistCarrier : BHistCarrier ValidatedNumericsUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := validatedNumericsToEventFlow
  fromEventFlow := validatedNumericsFromEventFlow

instance validatedNumericsChapterTasteGate : ChapterTasteGate ValidatedNumericsUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change validatedNumericsFromEventFlow (validatedNumericsToEventFlow x) = some x
    exact validatedNumerics_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (validatedNumericsToEventFlow_injective heq)

theorem ValidatedNumericsPacket_public_finite_enclosure_consumer_certificate
    [AskSetup] [PackageSetup]
    {interval precision modulus observation readback transport containment provenance name :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ValidatedNumericsPacket interval precision modulus observation readback transport containment
        provenance name bundle pkg ->
      Nonempty (ChapterTasteGate ValidatedNumericsUp) ∧
        SemanticNameCert
          (fun row : BHist => hsame row name ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            UnaryHistory interval ∧ UnaryHistory precision ∧ UnaryHistory modulus ∧
              Cont precision modulus observation ∧ Cont observation interval containment ∧
                hsame row name)
          (fun row : BHist => PkgSig bundle row pkg ∧ Cont containment provenance name)
          (fun row row' : BHist => PkgSig bundle row pkg ∧ hsame row row') := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig SemanticNameCert
  intro packet
  obtain ⟨intervalUnary, precisionUnary, modulusUnary, _observationUnary, _readbackUnary,
    _transportUnary, _containmentUnary, _provenanceUnary, nameUnary,
    precisionModulusObservation, _observationReadbackTransport,
    observationIntervalContainment, containmentProvenanceName, namePkg⟩ := packet
  have sourceAtName :
      hsame name name ∧ UnaryHistory name ∧ PkgSig bundle name pkg :=
    ⟨hsame_refl name, nameUnary, namePkg⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row name ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        (fun row : BHist =>
          UnaryHistory interval ∧ UnaryHistory precision ∧ UnaryHistory modulus ∧
            Cont precision modulus observation ∧ Cont observation interval containment ∧
              hsame row name)
        (fun row : BHist => PkgSig bundle row pkg ∧ Cont containment provenance name)
        (fun row row' : BHist => PkgSig bundle row pkg ∧ hsame row row') := {
    core := {
      carrier_inhabited := Exists.intro name sourceAtName
      equiv_refl := by
        intro row source
        exact ⟨source.right.right, hsame_refl row⟩
      equiv_symm := by
        intro row _other classified
        cases classified.right
        exact ⟨classified.left, hsame_refl row⟩
      equiv_trans := by
        intro _row _middle _other leftClassified rightClassified
        exact
          ⟨leftClassified.left, hsame_trans leftClassified.right rightClassified.right⟩
      carrier_respects_equiv := by
        intro _row _other classified source
        cases classified.right
        exact source
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨intervalUnary, precisionUnary, modulusUnary, precisionModulusObservation,
          observationIntervalContainment, source.left⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right.right, containmentProvenanceName⟩
  }
  exact ⟨⟨validatedNumericsChapterTasteGate⟩, cert⟩

end BEDC.Derived.ValidatedNumericsUp
