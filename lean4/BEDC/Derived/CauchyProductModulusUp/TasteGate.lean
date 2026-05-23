import BEDC.Derived.CauchyProductModulusUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyProductModulusUp

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

def cauchyProductModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyProductModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyProductModulusEncodeBHist h

def cauchyProductModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyProductModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyProductModulusDecodeBHist tail)

private theorem cauchyProductModulus_decode_encode_bhist :
    ∀ h : BHist,
      cauchyProductModulusDecodeBHist (cauchyProductModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyProductModulusFields : CauchyProductModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyProductModulusUp.mk sourceA sourceB windowA windowB dyadicA dyadicB budget
      modulus readback sealRow transport routes provenance name =>
      [sourceA, sourceB, windowA, windowB, dyadicA, dyadicB, budget, modulus, readback,
        sealRow, transport, routes, provenance, name]

def cauchyProductModulusToEventFlow : CauchyProductModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyProductModulusFields x).map cauchyProductModulusEncodeBHist

private def cauchyProductModulusEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyProductModulusEventAt index rest

private def cauchyProductModulusLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => true
  | Nat.zero, _event :: _rest => false
  | Nat.succ _index, [] => false
  | Nat.succ index, _event :: rest => cauchyProductModulusLengthEq index rest

def cauchyProductModulusFromEventFlow : EventFlow → Option CauchyProductModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match cauchyProductModulusLengthEq 14 flow with
      | true =>
          some
            (CauchyProductModulusUp.mk
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 0 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 1 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 2 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 3 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 4 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 5 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 6 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 7 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 8 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 9 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 10 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 11 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 12 flow))
              (cauchyProductModulusDecodeBHist (cauchyProductModulusEventAt 13 flow)))
      | false => none

private theorem cauchyProductModulus_mk_congr
    {sourceA sourceA' sourceB sourceB' windowA windowA' windowB windowB'
      dyadicA dyadicA' dyadicB dyadicB' budget budget' modulus modulus'
      readback readback' sealRow sealRow' transport transport' routes routes'
      provenance provenance' name name' : BHist}
    (hSourceA : sourceA' = sourceA) (hSourceB : sourceB' = sourceB)
    (hWindowA : windowA' = windowA) (hWindowB : windowB' = windowB)
    (hDyadicA : dyadicA' = dyadicA) (hDyadicB : dyadicB' = dyadicB)
    (hBudget : budget' = budget) (hModulus : modulus' = modulus)
    (hReadback : readback' = readback) (hSealRow : sealRow' = sealRow)
    (hTransport : transport' = transport) (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance) (hName : name' = name) :
    CauchyProductModulusUp.mk sourceA' sourceB' windowA' windowB' dyadicA' dyadicB'
        budget' modulus' readback' sealRow' transport' routes' provenance' name' =
      CauchyProductModulusUp.mk sourceA sourceB windowA windowB dyadicA dyadicB budget
        modulus readback sealRow transport routes provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSourceA
  cases hSourceB
  cases hWindowA
  cases hWindowB
  cases hDyadicA
  cases hDyadicB
  cases hBudget
  cases hModulus
  cases hReadback
  cases hSealRow
  cases hTransport
  cases hRoutes
  cases hProvenance
  cases hName
  rfl

private theorem cauchyProductModulus_round_trip :
    ∀ x : CauchyProductModulusUp,
      cauchyProductModulusFromEventFlow (cauchyProductModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceA sourceB windowA windowB dyadicA dyadicB budget modulus readback sealRow
      transport routes provenance name =>
      exact
        congrArg some
          (cauchyProductModulus_mk_congr
            (cauchyProductModulus_decode_encode_bhist sourceA)
            (cauchyProductModulus_decode_encode_bhist sourceB)
            (cauchyProductModulus_decode_encode_bhist windowA)
            (cauchyProductModulus_decode_encode_bhist windowB)
            (cauchyProductModulus_decode_encode_bhist dyadicA)
            (cauchyProductModulus_decode_encode_bhist dyadicB)
            (cauchyProductModulus_decode_encode_bhist budget)
            (cauchyProductModulus_decode_encode_bhist modulus)
            (cauchyProductModulus_decode_encode_bhist readback)
            (cauchyProductModulus_decode_encode_bhist sealRow)
            (cauchyProductModulus_decode_encode_bhist transport)
            (cauchyProductModulus_decode_encode_bhist routes)
            (cauchyProductModulus_decode_encode_bhist provenance)
            (cauchyProductModulus_decode_encode_bhist name))

private theorem cauchyProductModulusToEventFlow_injective {x y : CauchyProductModulusUp} :
    cauchyProductModulusToEventFlow x = cauchyProductModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyProductModulusFromEventFlow (cauchyProductModulusToEventFlow x) =
        cauchyProductModulusFromEventFlow (cauchyProductModulusToEventFlow y) :=
    congrArg cauchyProductModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyProductModulus_round_trip x).symm
      (Eq.trans hread (cauchyProductModulus_round_trip y)))

instance cauchyProductModulusBHistCarrier : BHistCarrier CauchyProductModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyProductModulusToEventFlow
  fromEventFlow := cauchyProductModulusFromEventFlow

instance cauchyProductModulusChapterTasteGate :
    ChapterTasteGate CauchyProductModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyProductModulusFromEventFlow (cauchyProductModulusToEventFlow x) = some x
    exact cauchyProductModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyProductModulusToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyProductModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyProductModulusChapterTasteGate

theorem CauchyProductModulusTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyProductModulusUp) ∧
      (∀ h : BHist, cauchyProductModulusDecodeBHist (cauchyProductModulusEncodeBHist h) = h) ∧
        (∀ x : CauchyProductModulusUp,
          cauchyProductModulusFromEventFlow (cauchyProductModulusToEventFlow x) = some x) ∧
          (∀ x y : CauchyProductModulusUp,
            cauchyProductModulusToEventFlow x = cauchyProductModulusToEventFlow y → x = y) ∧
            cauchyProductModulusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨cauchyProductModulusChapterTasteGate⟩,
      cauchyProductModulus_decode_encode_bhist,
      cauchyProductModulus_round_trip,
      (fun _ _ heq => cauchyProductModulusToEventFlow_injective heq),
      rfl⟩

namespace TasteGate

def CauchyProductModulusCarrier [AskSetup] [PackageSetup]
    (sourceA sourceB windowA windowB dyadicA dyadicB budget modulus readback sealRow
      transport routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
    UnaryHistory sourceA ∧
      UnaryHistory sourceB ∧
        UnaryHistory windowA ∧
          UnaryHistory windowB ∧
            UnaryHistory dyadicA ∧
              UnaryHistory dyadicB ∧
                UnaryHistory budget ∧
                  UnaryHistory modulus ∧
                    UnaryHistory readback ∧
                      Cont sourceA sourceB budget ∧
                        Cont budget modulus readback ∧
                          Cont readback sealRow transport ∧
                            Cont transport routes name ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle sealRow pkg ∧
                                  hsame sealRow readback ∧ hsame name sealRow

theorem CauchyProductModulusCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB dyadicA dyadicB budget modulus readback sealRow transport
      routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductModulusCarrier sourceA sourceB windowA windowB dyadicA dyadicB budget modulus
        readback sealRow transport routes provenance name bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceA ∨ hsame row sourceB ∨ hsame row budget ∨ hsame row modulus ∨
              hsame row readback ∨ hsame row sealRow)
          (fun row : BHist => hsame row sealRow ∧ PkgSig bundle sealRow pkg)
          hsame ∧
        Nonempty (ChapterTasteGate CauchyProductModulusUp) ∧
          PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _dyadicAUnary,
    _dyadicBUnary, _budgetUnary, _modulusUnary, readbackUnary, _sourceBudget,
    _budgetReadback, _readbackSealTransport, _transportRoutesName, provenancePkg, sealPkg,
    sameSealReadback, _sameNameSeal⟩ := carrier
  have sealUnary : UnaryHistory sealRow :=
    unary_transport readbackUnary (hsame_symm sameSealReadback)
  have sourceSeal : (fun row : BHist => hsame row sealRow ∧ UnaryHistory row) sealRow := by
    exact ⟨hsame_refl sealRow, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceA ∨ hsame row sourceB ∨ hsame row budget ∨ hsame row modulus ∨
              hsame row readback ∨ hsame row sealRow)
          (fun row : BHist => hsame row sealRow ∧ PkgSig bundle sealRow pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro sealRow sourceSeal
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, sealPkg⟩
    }
  exact ⟨cert, ⟨cauchyProductModulusChapterTasteGate⟩, provenancePkg⟩

def taste_gate : ChapterTasteGate CauchyProductModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BEDC.Derived.CauchyProductModulusUp.taste_gate

theorem CauchyProductModulusTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyProductModulusUp) ∧
      (∀ h : BHist, cauchyProductModulusDecodeBHist (cauchyProductModulusEncodeBHist h) = h) ∧
        (∀ x : CauchyProductModulusUp,
          cauchyProductModulusFromEventFlow (cauchyProductModulusToEventFlow x) = some x) ∧
          (∀ x y : CauchyProductModulusUp,
            cauchyProductModulusToEventFlow x = cauchyProductModulusToEventFlow y → x = y) ∧
            cauchyProductModulusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact BEDC.Derived.CauchyProductModulusUp.CauchyProductModulusTasteGate_single_carrier_alignment

end TasteGate

end BEDC.Derived.CauchyProductModulusUp
