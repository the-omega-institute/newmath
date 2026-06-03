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

namespace BEDC.Derived.RegulatedCauchyIntegralUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegulatedCauchyIntegralCarrier [AskSetup] [PackageSetup]
    (integrand partition step windows readback realSeal transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory integrand ∧ UnaryHistory partition ∧ UnaryHistory step ∧
    UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont transport replay provenance ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem RegulatedCauchyIntegralWindowReadbackExactness [AskSetup] [PackageSetup]
    {integrand partition step windows readback realSeal transport replay provenance localName
      partitionRead stepRead windowRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegulatedCauchyIntegralCarrier integrand partition step windows readback realSeal transport
        replay provenance localName bundle pkg →
      Cont integrand partition partitionRead →
        Cont partition step stepRead →
          Cont step windows windowRead →
            Cont windowRead readback sealRead →
              PkgSig bundle provenance pkg →
                PkgSig bundle localName pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row integrand ∨ hsame row partition ∨ hsame row step ∨
                          hsame row windows ∨ hsame row readback ∨ hsame row sealRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle localName pkg)
                      hsame ∧
                    UnaryHistory partitionRead ∧ UnaryHistory stepRead ∧
                      UnaryHistory windowRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier integrandPartition partitionStep stepWindows windowReadReadback
    provenancePkg localNamePkg
  obtain ⟨integrandUnary, partitionUnary, stepUnary, windowsUnary, readbackUnary,
    _realSealUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _transportReplayProvenance, _carrierProvenancePkg, _carrierLocalNamePkg⟩ := carrier
  have partitionReadUnary : UnaryHistory partitionRead :=
    unary_cont_closed integrandUnary partitionUnary integrandPartition
  have stepReadUnary : UnaryHistory stepRead :=
    unary_cont_closed partitionUnary stepUnary partitionStep
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed stepUnary windowsUnary stepWindows
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed windowReadUnary readbackUnary windowReadReadback
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row integrand ∨ hsame row partition ∨ hsame row step ∨
              hsame row windows ∨ hsame row readback ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, partitionReadUnary, stepReadUnary, windowReadUnary, sealReadUnary⟩

end BEDC.Derived.RegulatedCauchyIntegralUp

namespace BEDC.Derived.RegulatedCauchyIntegralUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegulatedCauchyIntegralUp : Type where
  | mk (G T A W R E H C P N : BHist) : RegulatedCauchyIntegralUp
  deriving DecidableEq

def regulatedCauchyIntegralEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regulatedCauchyIntegralEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regulatedCauchyIntegralEncodeBHist h

def regulatedCauchyIntegralDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regulatedCauchyIntegralDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regulatedCauchyIntegralDecodeBHist tail)

private theorem RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regulatedCauchyIntegralDecodeBHist (regulatedCauchyIntegralEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regulatedCauchyIntegralFields : RegulatedCauchyIntegralUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegulatedCauchyIntegralUp.mk G T A W R E H C P N => [G, T, A, W, R, E, H, C, P, N]

def regulatedCauchyIntegralToEventFlow : RegulatedCauchyIntegralUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regulatedCauchyIntegralFields x).map regulatedCauchyIntegralEncodeBHist

private def RegulatedCauchyIntegralTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RegulatedCauchyIntegralTasteGate_single_carrier_alignment_eventAt index rest

def regulatedCauchyIntegralFromEventFlow : EventFlow → Option RegulatedCauchyIntegralUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegulatedCauchyIntegralUp.mk
        (regulatedCauchyIntegralDecodeBHist
          (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_eventAt 0 ef))
        (regulatedCauchyIntegralDecodeBHist
          (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_eventAt 1 ef))
        (regulatedCauchyIntegralDecodeBHist
          (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_eventAt 2 ef))
        (regulatedCauchyIntegralDecodeBHist
          (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_eventAt 3 ef))
        (regulatedCauchyIntegralDecodeBHist
          (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_eventAt 4 ef))
        (regulatedCauchyIntegralDecodeBHist
          (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_eventAt 5 ef))
        (regulatedCauchyIntegralDecodeBHist
          (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_eventAt 6 ef))
        (regulatedCauchyIntegralDecodeBHist
          (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_eventAt 7 ef))
        (regulatedCauchyIntegralDecodeBHist
          (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_eventAt 8 ef))
        (regulatedCauchyIntegralDecodeBHist
          (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem RegulatedCauchyIntegralTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegulatedCauchyIntegralUp,
      regulatedCauchyIntegralFromEventFlow (regulatedCauchyIntegralToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G T A W R E H C P N =>
      change
        some
          (RegulatedCauchyIntegralUp.mk
            (regulatedCauchyIntegralDecodeBHist (regulatedCauchyIntegralEncodeBHist G))
            (regulatedCauchyIntegralDecodeBHist (regulatedCauchyIntegralEncodeBHist T))
            (regulatedCauchyIntegralDecodeBHist (regulatedCauchyIntegralEncodeBHist A))
            (regulatedCauchyIntegralDecodeBHist (regulatedCauchyIntegralEncodeBHist W))
            (regulatedCauchyIntegralDecodeBHist (regulatedCauchyIntegralEncodeBHist R))
            (regulatedCauchyIntegralDecodeBHist (regulatedCauchyIntegralEncodeBHist E))
            (regulatedCauchyIntegralDecodeBHist (regulatedCauchyIntegralEncodeBHist H))
            (regulatedCauchyIntegralDecodeBHist (regulatedCauchyIntegralEncodeBHist C))
            (regulatedCauchyIntegralDecodeBHist (regulatedCauchyIntegralEncodeBHist P))
            (regulatedCauchyIntegralDecodeBHist (regulatedCauchyIntegralEncodeBHist N))) =
          some (RegulatedCauchyIntegralUp.mk G T A W R E H C P N)
      rw [RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode G,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode T,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode A,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode W,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode R,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode E,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode H,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode C,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode P,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode N]

private theorem RegulatedCauchyIntegralTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegulatedCauchyIntegralUp} :
    regulatedCauchyIntegralToEventFlow x = regulatedCauchyIntegralToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regulatedCauchyIntegralFromEventFlow (regulatedCauchyIntegralToEventFlow x) =
        regulatedCauchyIntegralFromEventFlow (regulatedCauchyIntegralToEventFlow y) :=
    congrArg regulatedCauchyIntegralFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_round_trip y)))

instance regulatedCauchyIntegralBHistCarrier : BHistCarrier RegulatedCauchyIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regulatedCauchyIntegralToEventFlow
  fromEventFlow := regulatedCauchyIntegralFromEventFlow

instance regulatedCauchyIntegralChapterTasteGate :
    ChapterTasteGate RegulatedCauchyIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regulatedCauchyIntegralFromEventFlow (regulatedCauchyIntegralToEventFlow x) = some x
    exact RegulatedCauchyIntegralTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RegulatedCauchyIntegralTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regulatedCauchyIntegralDecodeBHist (regulatedCauchyIntegralEncodeBHist h) = h) ∧
      (∀ x : RegulatedCauchyIntegralUp,
        regulatedCauchyIntegralFromEventFlow (regulatedCauchyIntegralToEventFlow x) = some x) ∧
        (∀ x y : RegulatedCauchyIntegralUp,
          regulatedCauchyIntegralToEventFlow x = regulatedCauchyIntegralToEventFlow y →
            x = y) ∧
          regulatedCauchyIntegralEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode,
      RegulatedCauchyIntegralTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegulatedCauchyIntegralUp.TasteGate
