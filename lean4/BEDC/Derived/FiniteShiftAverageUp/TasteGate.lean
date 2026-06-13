import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteShiftAverageUp

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

inductive FiniteShiftAverageUp : Type where
  | mk (stream window average dyadic readback sealRow transport replay provenance localName : BHist) :
      FiniteShiftAverageUp
  deriving DecidableEq

def finiteShiftAverageEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteShiftAverageEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteShiftAverageEncodeBHist h

def finiteShiftAverageDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteShiftAverageDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteShiftAverageDecodeBHist tail)

theorem FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux :
    ∀ h : BHist, finiteShiftAverageDecodeBHist (finiteShiftAverageEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

theorem FiniteShiftAverageTasteGate_single_carrier_alignment_mk_congr_aux
    {stream₁ window₁ average₁ dyadic₁ readback₁ sealRow₁ transport₁ replay₁ provenance₁
      localName₁ stream₂ window₂ average₂ dyadic₂ readback₂ sealRow₂ transport₂ replay₂
      provenance₂ localName₂ : BHist} :
    stream₁ = stream₂ →
      window₁ = window₂ →
        average₁ = average₂ →
          dyadic₁ = dyadic₂ →
            readback₁ = readback₂ →
              sealRow₁ = sealRow₂ →
                transport₁ = transport₂ →
                  replay₁ = replay₂ →
                    provenance₁ = provenance₂ →
                      localName₁ = localName₂ →
                        FiniteShiftAverageUp.mk stream₁ window₁ average₁ dyadic₁ readback₁
                            sealRow₁ transport₁ replay₁ provenance₁ localName₁ =
                          FiniteShiftAverageUp.mk stream₂ window₂ average₂ dyadic₂ readback₂
                            sealRow₂ transport₂ replay₂ provenance₂ localName₂ := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hstream hwindow haverage hdyadic hreadback hsealRow htransport hreplay hprovenance
    hlocalName
  cases hstream
  cases hwindow
  cases haverage
  cases hdyadic
  cases hreadback
  cases hsealRow
  cases htransport
  cases hreplay
  cases hprovenance
  cases hlocalName
  rfl

def finiteShiftAverageToEventFlow : FiniteShiftAverageUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteShiftAverageUp.mk stream window average dyadic readback sealRow transport replay
      provenance localName =>
      [finiteShiftAverageEncodeBHist stream,
        finiteShiftAverageEncodeBHist window,
        finiteShiftAverageEncodeBHist average,
        finiteShiftAverageEncodeBHist dyadic,
        finiteShiftAverageEncodeBHist readback,
        finiteShiftAverageEncodeBHist sealRow,
        finiteShiftAverageEncodeBHist transport,
        finiteShiftAverageEncodeBHist replay,
        finiteShiftAverageEncodeBHist provenance,
        finiteShiftAverageEncodeBHist localName]

def finiteShiftAverageFromEventFlow : EventFlow → Option FiniteShiftAverageUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | stream :: rest0 =>
      match rest0 with
      | [] => none
      | window :: rest1 =>
          match rest1 with
          | [] => none
          | average :: rest2 =>
              match rest2 with
              | [] => none
              | dyadic :: rest3 =>
                  match rest3 with
                  | [] => none
                  | readback :: rest4 =>
                      match rest4 with
                      | [] => none
                      | sealRow :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | replay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | localName :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (FiniteShiftAverageUp.mk
                                                  (finiteShiftAverageDecodeBHist stream)
                                                  (finiteShiftAverageDecodeBHist window)
                                                  (finiteShiftAverageDecodeBHist average)
                                                  (finiteShiftAverageDecodeBHist dyadic)
                                                  (finiteShiftAverageDecodeBHist readback)
                                                  (finiteShiftAverageDecodeBHist sealRow)
                                                  (finiteShiftAverageDecodeBHist transport)
                                                  (finiteShiftAverageDecodeBHist replay)
                                                  (finiteShiftAverageDecodeBHist provenance)
                                                  (finiteShiftAverageDecodeBHist localName))
                                          | _ :: _ => none

theorem FiniteShiftAverageTasteGate_single_carrier_alignment_round_trip_aux :
    ∀ x : FiniteShiftAverageUp,
      finiteShiftAverageFromEventFlow (finiteShiftAverageToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk stream window average dyadic readback sealRow transport replay provenance localName =>
      exact
        congrArg some
          (FiniteShiftAverageTasteGate_single_carrier_alignment_mk_congr_aux
            (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux stream)
            (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux window)
            (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux average)
            (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux dyadic)
            (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux readback)
            (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux sealRow)
            (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux transport)
            (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux replay)
            (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux provenance)
            (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux localName))

theorem FiniteShiftAverageTasteGate_single_carrier_alignment_toEventFlow_injective_aux
    {x y : FiniteShiftAverageUp} :
    finiteShiftAverageToEventFlow x = finiteShiftAverageToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk stream₁ window₁ average₁ dyadic₁ readback₁ sealRow₁ transport₁ replay₁
      provenance₁ localName₁ =>
      cases y with
      | mk stream₂ window₂ average₂ dyadic₂ readback₂ sealRow₂ transport₂ replay₂
          provenance₂ localName₂ =>
          change
            [finiteShiftAverageEncodeBHist stream₁, finiteShiftAverageEncodeBHist window₁,
              finiteShiftAverageEncodeBHist average₁, finiteShiftAverageEncodeBHist dyadic₁,
              finiteShiftAverageEncodeBHist readback₁, finiteShiftAverageEncodeBHist sealRow₁,
              finiteShiftAverageEncodeBHist transport₁, finiteShiftAverageEncodeBHist replay₁,
              finiteShiftAverageEncodeBHist provenance₁,
              finiteShiftAverageEncodeBHist localName₁] =
            [finiteShiftAverageEncodeBHist stream₂, finiteShiftAverageEncodeBHist window₂,
              finiteShiftAverageEncodeBHist average₂, finiteShiftAverageEncodeBHist dyadic₂,
              finiteShiftAverageEncodeBHist readback₂, finiteShiftAverageEncodeBHist sealRow₂,
              finiteShiftAverageEncodeBHist transport₂, finiteShiftAverageEncodeBHist replay₂,
              finiteShiftAverageEncodeBHist provenance₂,
              finiteShiftAverageEncodeBHist localName₂] at heq
          injection heq with hstream t0
          injection t0 with hwindow t1
          injection t1 with haverage t2
          injection t2 with hdyadic t3
          injection t3 with hreadback t4
          injection t4 with hsealRow t5
          injection t5 with htransport t6
          injection t6 with hreplay t7
          injection t7 with hprovenance t8
          injection t8 with hlocalName _
          have streamEq : stream₁ = stream₂ := by
            exact
              Eq.trans
                (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux stream₁).symm
                (Eq.trans (congrArg finiteShiftAverageDecodeBHist hstream)
                  (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux stream₂))
          have windowEq : window₁ = window₂ := by
            exact
              Eq.trans
                (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux window₁).symm
                (Eq.trans (congrArg finiteShiftAverageDecodeBHist hwindow)
                  (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux window₂))
          have averageEq : average₁ = average₂ := by
            exact
              Eq.trans
                (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux average₁).symm
                (Eq.trans (congrArg finiteShiftAverageDecodeBHist haverage)
                  (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux average₂))
          have dyadicEq : dyadic₁ = dyadic₂ := by
            exact
              Eq.trans
                (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux dyadic₁).symm
                (Eq.trans (congrArg finiteShiftAverageDecodeBHist hdyadic)
                  (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux dyadic₂))
          have readbackEq : readback₁ = readback₂ := by
            exact
              Eq.trans
                (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux readback₁).symm
                (Eq.trans (congrArg finiteShiftAverageDecodeBHist hreadback)
                  (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux readback₂))
          have sealRowEq : sealRow₁ = sealRow₂ := by
            exact
              Eq.trans
                (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux sealRow₁).symm
                (Eq.trans (congrArg finiteShiftAverageDecodeBHist hsealRow)
                  (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux sealRow₂))
          have transportEq : transport₁ = transport₂ := by
            exact
              Eq.trans
                (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux transport₁).symm
                (Eq.trans (congrArg finiteShiftAverageDecodeBHist htransport)
                  (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux transport₂))
          have replayEq : replay₁ = replay₂ := by
            exact
              Eq.trans
                (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux replay₁).symm
                (Eq.trans (congrArg finiteShiftAverageDecodeBHist hreplay)
                  (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux replay₂))
          have provenanceEq : provenance₁ = provenance₂ := by
            exact
              Eq.trans
                (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux provenance₁).symm
                (Eq.trans (congrArg finiteShiftAverageDecodeBHist hprovenance)
                  (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux provenance₂))
          have localNameEq : localName₁ = localName₂ := by
            exact
              Eq.trans
                (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux localName₁).symm
                (Eq.trans (congrArg finiteShiftAverageDecodeBHist hlocalName)
                  (FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux localName₂))
          cases streamEq
          cases windowEq
          cases averageEq
          cases dyadicEq
          cases readbackEq
          cases sealRowEq
          cases transportEq
          cases replayEq
          cases provenanceEq
          cases localNameEq
          rfl

instance finiteShiftAverageBHistCarrier : BHistCarrier FiniteShiftAverageUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteShiftAverageToEventFlow
  fromEventFlow := finiteShiftAverageFromEventFlow

instance finiteShiftAverageChapterTasteGate : ChapterTasteGate FiniteShiftAverageUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteShiftAverageFromEventFlow (finiteShiftAverageToEventFlow x) = some x
    exact FiniteShiftAverageTasteGate_single_carrier_alignment_round_trip_aux x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteShiftAverageTasteGate_single_carrier_alignment_toEventFlow_injective_aux heq)

def taste_gate : ChapterTasteGate FiniteShiftAverageUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteShiftAverageChapterTasteGate

theorem FiniteShiftAverageTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteShiftAverageDecodeBHist (finiteShiftAverageEncodeBHist h) = h) ∧
      (∀ x : FiniteShiftAverageUp,
        finiteShiftAverageFromEventFlow (finiteShiftAverageToEventFlow x) = some x) ∧
      (∀ x y : FiniteShiftAverageUp,
        finiteShiftAverageToEventFlow x = finiteShiftAverageToEventFlow y → x = y) ∧
      finiteShiftAverageEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    exact FiniteShiftAverageTasteGate_single_carrier_alignment_decode_aux h
  · constructor
    · intro x
      exact FiniteShiftAverageTasteGate_single_carrier_alignment_round_trip_aux x
    · constructor
      · intro x y heq
        exact FiniteShiftAverageTasteGate_single_carrier_alignment_toEventFlow_injective_aux heq
      · rfl

def FiniteShiftAverageCarrier [AskSetup] [PackageSetup]
    (stream window average dyadic readback sealRow transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory stream ∧ UnaryHistory window ∧ UnaryHistory average ∧ UnaryHistory dyadic ∧
    UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont stream window transport ∧ Cont transport average replay ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem FiniteShiftAverageCarrier_banach_limit_boundary [AskSetup] [PackageSetup]
    {stream window average dyadic readback sealRow transport replay provenance localName
      windowRead averageRead toleranceRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteShiftAverageCarrier stream window average dyadic readback sealRow transport replay
        provenance localName bundle pkg →
      Cont stream window windowRead →
        Cont windowRead average averageRead →
          Cont averageRead dyadic toleranceRead →
            Cont toleranceRead sealRow sealRead →
              PkgSig bundle sealRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row stream ∨ hsame row window ∨ hsame row average ∨
                        hsame row dyadic ∨ hsame row readback ∨ hsame row sealRow ∨
                          hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont stream window windowRead ∧
                        Cont windowRead average averageRead ∧
                          Cont averageRead dyadic toleranceRead ∧
                            Cont toleranceRead sealRow sealRead ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg)
                    hsame ∧
                  UnaryHistory windowRead ∧ UnaryHistory averageRead ∧
                    UnaryHistory toleranceRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier windowRoute averageRoute toleranceRoute sealRoute sealPkg
  obtain ⟨streamUnary, windowUnary, averageUnary, dyadicUnary, _readbackUnary, sealRowUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _carrierWindowRoute,
    _carrierReplayRoute, provenancePkg, _localNamePkg⟩ := carrier
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed streamUnary windowUnary windowRoute
  have averageReadUnary : UnaryHistory averageRead :=
    unary_cont_closed windowReadUnary averageUnary averageRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed averageReadUnary dyadicUnary toleranceRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceReadUnary sealRowUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row window ∨ hsame row average ∨ hsame row dyadic ∨
              hsame row readback ∨ hsame row sealRow ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont stream window windowRead ∧
              Cont windowRead average averageRead ∧ Cont averageRead dyadic toleranceRead ∧
                Cont toleranceRead sealRow sealRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, averageRoute, toleranceRoute, sealRoute, provenancePkg,
          sealPkg⟩
  }
  exact ⟨cert, windowReadUnary, averageReadUnary, toleranceReadUnary, sealReadUnary⟩

end BEDC.Derived.FiniteShiftAverageUp
