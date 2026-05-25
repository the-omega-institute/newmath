import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCauchySumUp

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

inductive RealCauchySumUp : Type where
  | mk :
      (term partialSum windows readback dyadic modulus sealRow transport replay provenance
        localName : BHist) →
      RealCauchySumUp
  deriving DecidableEq

def realCauchySumEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCauchySumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCauchySumEncodeBHist h

def realCauchySumDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCauchySumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCauchySumDecodeBHist tail)

private theorem realCauchySum_decode_encode_bhist :
    ∀ h : BHist, realCauchySumDecodeBHist (realCauchySumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realCauchySumToEventFlow : RealCauchySumUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealCauchySumUp.mk term partialSum windows readback dyadic modulus sealRow transport
      replay provenance localName =>
      [realCauchySumEncodeBHist term,
        realCauchySumEncodeBHist partialSum,
        realCauchySumEncodeBHist windows,
        realCauchySumEncodeBHist readback,
        realCauchySumEncodeBHist dyadic,
        realCauchySumEncodeBHist modulus,
        realCauchySumEncodeBHist sealRow,
        realCauchySumEncodeBHist transport,
        realCauchySumEncodeBHist replay,
        realCauchySumEncodeBHist provenance,
        realCauchySumEncodeBHist localName]

def realCauchySumFromEventFlow : EventFlow → Option RealCauchySumUp
  -- BEDC touchpoint anchor: BHist BMark
  | term :: partialSum :: windows :: readback :: dyadic :: modulus :: sealRow ::
      transport :: replay :: provenance :: localName :: [] =>
      some
        (RealCauchySumUp.mk
          (realCauchySumDecodeBHist term)
          (realCauchySumDecodeBHist partialSum)
          (realCauchySumDecodeBHist windows)
          (realCauchySumDecodeBHist readback)
          (realCauchySumDecodeBHist dyadic)
          (realCauchySumDecodeBHist modulus)
          (realCauchySumDecodeBHist sealRow)
          (realCauchySumDecodeBHist transport)
          (realCauchySumDecodeBHist replay)
          (realCauchySumDecodeBHist provenance)
          (realCauchySumDecodeBHist localName))
  | _ => none

private theorem realCauchySum_round_trip :
    ∀ x : RealCauchySumUp,
      realCauchySumFromEventFlow (realCauchySumToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk term partialSum windows readback dyadic modulus sealRow transport replay provenance
      localName =>
      change
        some
          (RealCauchySumUp.mk
            (realCauchySumDecodeBHist (realCauchySumEncodeBHist term))
            (realCauchySumDecodeBHist (realCauchySumEncodeBHist partialSum))
            (realCauchySumDecodeBHist (realCauchySumEncodeBHist windows))
            (realCauchySumDecodeBHist (realCauchySumEncodeBHist readback))
            (realCauchySumDecodeBHist (realCauchySumEncodeBHist dyadic))
            (realCauchySumDecodeBHist (realCauchySumEncodeBHist modulus))
            (realCauchySumDecodeBHist (realCauchySumEncodeBHist sealRow))
            (realCauchySumDecodeBHist (realCauchySumEncodeBHist transport))
            (realCauchySumDecodeBHist (realCauchySumEncodeBHist replay))
            (realCauchySumDecodeBHist (realCauchySumEncodeBHist provenance))
            (realCauchySumDecodeBHist (realCauchySumEncodeBHist localName))) =
          some
            (RealCauchySumUp.mk term partialSum windows readback dyadic modulus sealRow
              transport replay provenance localName)
      rw [realCauchySum_decode_encode_bhist term,
        realCauchySum_decode_encode_bhist partialSum,
        realCauchySum_decode_encode_bhist windows,
        realCauchySum_decode_encode_bhist readback,
        realCauchySum_decode_encode_bhist dyadic,
        realCauchySum_decode_encode_bhist modulus,
        realCauchySum_decode_encode_bhist sealRow,
        realCauchySum_decode_encode_bhist transport,
        realCauchySum_decode_encode_bhist replay,
        realCauchySum_decode_encode_bhist provenance,
        realCauchySum_decode_encode_bhist localName]

private theorem realCauchySumToEventFlow_injective {x y : RealCauchySumUp} :
    realCauchySumToEventFlow x = realCauchySumToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCauchySumFromEventFlow (realCauchySumToEventFlow x) =
        realCauchySumFromEventFlow (realCauchySumToEventFlow y) :=
    congrArg realCauchySumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCauchySum_round_trip x).symm
      (Eq.trans hread (realCauchySum_round_trip y)))

instance realCauchySumBHistCarrier : BHistCarrier RealCauchySumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCauchySumToEventFlow
  fromEventFlow := realCauchySumFromEventFlow

instance realCauchySumChapterTasteGate : ChapterTasteGate RealCauchySumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := realCauchySum_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCauchySumToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealCauchySumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realCauchySumChapterTasteGate

structure RealCauchySumCarrier [AskSetup] [PackageSetup]
    (term partialSum windows readback dyadic modulus sealRow transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop where
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  term_unary : UnaryHistory term
  partialSum_unary : UnaryHistory partialSum
  windows_unary : UnaryHistory windows
  readback_unary : UnaryHistory readback
  dyadic_unary : UnaryHistory dyadic
  modulus_unary : UnaryHistory modulus
  sealRow_unary : UnaryHistory sealRow
  transport_unary : UnaryHistory transport
  replay_unary : UnaryHistory replay
  provenance_unary : UnaryHistory provenance
  localName_unary : UnaryHistory localName
  term_partialSum_windows : Cont term partialSum windows
  windows_readback_dyadic : Cont windows readback dyadic
  dyadic_modulus_sealRow : Cont dyadic modulus sealRow
  transport_replay_localName : Cont transport replay localName
  provenance_pkg : PkgSig bundle provenance pkg
  localName_pkg : PkgSig bundle localName pkg

theorem RealCauchySumCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {term partialSum windows readback dyadic modulus sealRow transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchySumCarrier term partialSum windows readback dyadic modulus sealRow transport
        replay provenance localName bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          RealCauchySumCarrier term partialSum windows readback dyadic modulus sealRow
              transport replay provenance localName bundle pkg ∧
            (hsame row term ∨ hsame row partialSum ∨ hsame row windows ∨
              hsame row readback ∨ hsame row dyadic ∨ hsame row modulus ∨
                hsame row sealRow ∨ hsame row localName))
        (fun row : BHist =>
          Cont term partialSum windows ∧ Cont windows readback dyadic ∧
            Cont dyadic modulus sealRow ∧ Cont transport replay localName ∧
              (hsame row term ∨ hsame row partialSum ∨ hsame row windows ∨
                hsame row readback ∨ hsame row dyadic ∨ hsame row modulus ∨
                  hsame row sealRow ∨ hsame row localName))
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro localName
          ⟨carrier, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (hsame_refl localName)))))))⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        refine ⟨source.left, ?_⟩
        cases source.right with
        | inl rowTerm =>
            exact Or.inl (hsame_trans (hsame_symm same) rowTerm)
        | inr tail =>
            cases tail with
            | inl rowPartial =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm same) rowPartial))
            | inr tail' =>
                cases tail' with
                | inl rowWindows =>
                    exact Or.inr
                      (Or.inr (Or.inl (hsame_trans (hsame_symm same) rowWindows)))
                | inr tail'' =>
                    cases tail'' with
                    | inl rowReadback =>
                        exact Or.inr
                          (Or.inr (Or.inr (Or.inl
                            (hsame_trans (hsame_symm same) rowReadback))))
                    | inr tail''' =>
                        cases tail''' with
                        | inl rowDyadic =>
                            exact Or.inr
                              (Or.inr (Or.inr (Or.inr (Or.inl
                                (hsame_trans (hsame_symm same) rowDyadic)))))
                        | inr tail'''' =>
                            cases tail'''' with
                            | inl rowModulus =>
                                exact Or.inr
                                  (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                                    (hsame_trans (hsame_symm same) rowModulus))))))
                            | inr tail''''' =>
                                cases tail''''' with
                                | inl rowSeal =>
                                    exact Or.inr
                                      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                        (Or.inl
                                          (hsame_trans (hsame_symm same)
                                            rowSeal)))))))
                                | inr rowName =>
                                    exact Or.inr
                                      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                        (Or.inr
                                          (hsame_trans (hsame_symm same)
                                            rowName)))))))
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨carrier.term_partialSum_windows, carrier.windows_readback_dyadic,
          carrier.dyadic_modulus_sealRow, carrier.transport_replay_localName,
          source.right⟩
    ledger_sound := by
      intro _row source
      cases source.right with
      | inl rowTerm =>
          cases rowTerm
          exact ⟨carrier.term_unary, carrier.provenance_pkg⟩
      | inr tail =>
          cases tail with
          | inl rowPartial =>
              cases rowPartial
              exact ⟨carrier.partialSum_unary, carrier.provenance_pkg⟩
          | inr tail' =>
              cases tail' with
              | inl rowWindows =>
                  cases rowWindows
                  exact ⟨carrier.windows_unary, carrier.provenance_pkg⟩
              | inr tail'' =>
                  cases tail'' with
                  | inl rowReadback =>
                      cases rowReadback
                      exact ⟨carrier.readback_unary, carrier.provenance_pkg⟩
                  | inr tail''' =>
                      cases tail''' with
                      | inl rowDyadic =>
                          cases rowDyadic
                          exact ⟨carrier.dyadic_unary, carrier.provenance_pkg⟩
                      | inr tail'''' =>
                          cases tail'''' with
                          | inl rowModulus =>
                              cases rowModulus
                              exact ⟨carrier.modulus_unary, carrier.provenance_pkg⟩
                          | inr tail''''' =>
                              cases tail''''' with
                              | inl rowSeal =>
                                  cases rowSeal
                                  exact ⟨carrier.sealRow_unary, carrier.provenance_pkg⟩
                              | inr rowName =>
                                  cases rowName
                                  exact ⟨carrier.localName_unary, carrier.provenance_pkg⟩
  }

end BEDC.Derived.RealCauchySumUp
