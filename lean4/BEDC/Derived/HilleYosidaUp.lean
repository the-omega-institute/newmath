import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HilleYosidaUp

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

inductive HilleYosidaUp : Type where
  | mk (B A R S N H C P L : BHist) : HilleYosidaUp
  deriving DecidableEq

def hilleYosidaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hilleYosidaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hilleYosidaEncodeBHist h

def hilleYosidaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hilleYosidaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hilleYosidaDecodeBHist tail)

private theorem hilleYosidaDecode_encode_bhist :
    ∀ h : BHist, hilleYosidaDecodeBHist (hilleYosidaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hilleYosidaFields : HilleYosidaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HilleYosidaUp.mk B A R S N H C P L => [B, A, R, S, N, H, C, P, L]

def hilleYosidaToEventFlow : HilleYosidaUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (hilleYosidaFields x).map hilleYosidaEncodeBHist

private def hilleYosidaEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hilleYosidaEventAtDefault index rest

def hilleYosidaFromEventFlow (ef : EventFlow) : Option HilleYosidaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HilleYosidaUp.mk
      (hilleYosidaDecodeBHist (hilleYosidaEventAtDefault 0 ef))
      (hilleYosidaDecodeBHist (hilleYosidaEventAtDefault 1 ef))
      (hilleYosidaDecodeBHist (hilleYosidaEventAtDefault 2 ef))
      (hilleYosidaDecodeBHist (hilleYosidaEventAtDefault 3 ef))
      (hilleYosidaDecodeBHist (hilleYosidaEventAtDefault 4 ef))
      (hilleYosidaDecodeBHist (hilleYosidaEventAtDefault 5 ef))
      (hilleYosidaDecodeBHist (hilleYosidaEventAtDefault 6 ef))
      (hilleYosidaDecodeBHist (hilleYosidaEventAtDefault 7 ef))
      (hilleYosidaDecodeBHist (hilleYosidaEventAtDefault 8 ef)))

private theorem hilleYosida_round_trip :
    ∀ x : HilleYosidaUp,
      hilleYosidaFromEventFlow (hilleYosidaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B A R S N H C P L =>
      change
        some
          (HilleYosidaUp.mk
            (hilleYosidaDecodeBHist (hilleYosidaEncodeBHist B))
            (hilleYosidaDecodeBHist (hilleYosidaEncodeBHist A))
            (hilleYosidaDecodeBHist (hilleYosidaEncodeBHist R))
            (hilleYosidaDecodeBHist (hilleYosidaEncodeBHist S))
            (hilleYosidaDecodeBHist (hilleYosidaEncodeBHist N))
            (hilleYosidaDecodeBHist (hilleYosidaEncodeBHist H))
            (hilleYosidaDecodeBHist (hilleYosidaEncodeBHist C))
            (hilleYosidaDecodeBHist (hilleYosidaEncodeBHist P))
            (hilleYosidaDecodeBHist (hilleYosidaEncodeBHist L))) =
          some (HilleYosidaUp.mk B A R S N H C P L)
      rw [hilleYosidaDecode_encode_bhist B, hilleYosidaDecode_encode_bhist A,
        hilleYosidaDecode_encode_bhist R, hilleYosidaDecode_encode_bhist S,
        hilleYosidaDecode_encode_bhist N, hilleYosidaDecode_encode_bhist H,
        hilleYosidaDecode_encode_bhist C, hilleYosidaDecode_encode_bhist P,
        hilleYosidaDecode_encode_bhist L]

private theorem hilleYosidaToEventFlow_injective {x y : HilleYosidaUp} :
    hilleYosidaToEventFlow x = hilleYosidaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hilleYosidaFromEventFlow (hilleYosidaToEventFlow x) =
        hilleYosidaFromEventFlow (hilleYosidaToEventFlow y) :=
    congrArg hilleYosidaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hilleYosida_round_trip x).symm
      (Eq.trans hread (hilleYosida_round_trip y)))

instance hilleYosidaBHistCarrier : BHistCarrier HilleYosidaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hilleYosidaToEventFlow
  fromEventFlow := hilleYosidaFromEventFlow

instance hilleYosidaChapterTasteGate : ChapterTasteGate HilleYosidaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hilleYosidaFromEventFlow (hilleYosidaToEventFlow x) = some x
    exact hilleYosida_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hilleYosidaToEventFlow_injective heq)

def taste_gate : ChapterTasteGate HilleYosidaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hilleYosidaChapterTasteGate

theorem HilleYosidaTasteGate_single_carrier_alignment :
    (∀ h : BHist, hilleYosidaDecodeBHist (hilleYosidaEncodeBHist h) = h) ∧
      (∀ x : HilleYosidaUp,
        hilleYosidaFromEventFlow (hilleYosidaToEventFlow x) = some x) ∧
        (∀ x y : HilleYosidaUp,
          hilleYosidaToEventFlow x = hilleYosidaToEventFlow y → x = y) ∧
          hilleYosidaEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨hilleYosidaDecode_encode_bhist, hilleYosida_round_trip,
      (fun x y heq => hilleYosidaToEventFlow_injective heq), rfl⟩

theorem HilleYosidaCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {B A R S N H C P L graphRead resolventRead semigroupRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B -> UnaryHistory A -> UnaryHistory R -> UnaryHistory S ->
      UnaryHistory N -> UnaryHistory C -> Cont B A graphRead ->
        Cont graphRead R resolventRead -> Cont resolventRead S semigroupRead ->
          Cont semigroupRead C replayRead -> PkgSig bundle P pkg ->
            PkgSig bundle L pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row B ∨ hsame row A ∨ hsame row R ∨ hsame row S ∨
                      hsame row N ∨ hsame row C ∨ hsame row replayRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont B A graphRead ∧
                      Cont graphRead R resolventRead ∧
                        Cont resolventRead S semigroupRead ∧
                          Cont semigroupRead C replayRead ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle L pkg)
                  hsame ∧
                UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro bUnary aUnary rUnary sUnary _nUnary cUnary graphRoute resolventRoute
    semigroupRoute replayRoute provenancePkg localNamePkg
  have graphUnary : UnaryHistory graphRead :=
    unary_cont_closed bUnary aUnary graphRoute
  have resolventUnary : UnaryHistory resolventRead :=
    unary_cont_closed graphUnary rUnary resolventRoute
  have semigroupUnary : UnaryHistory semigroupRead :=
    unary_cont_closed resolventUnary sUnary semigroupRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed semigroupUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row A ∨ hsame row R ∨ hsame row S ∨ hsame row N ∨
              hsame row C ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B A graphRead ∧ Cont graphRead R resolventRead ∧
              Cont resolventRead S semigroupRead ∧ Cont semigroupRead C replayRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle L pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
        ⟨source.right, graphRoute, resolventRoute, semigroupRoute, replayRoute,
          provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, replayUnary⟩

theorem HilleYosidaSemigroupGeneratorHandoff [AskSetup] [PackageSetup]
    {B A R S N H C P L graphRead resolventRead semigroupRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B -> UnaryHistory A -> UnaryHistory R -> UnaryHistory S ->
      UnaryHistory N -> UnaryHistory C -> Cont B A graphRead ->
        Cont graphRead R resolventRead -> Cont resolventRead S semigroupRead ->
          Cont semigroupRead C replayRead -> PkgSig bundle P pkg ->
            PkgSig bundle L pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row semigroupRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row B ∨ hsame row A ∨ hsame row R ∨ hsame row S ∨
                      hsame row N ∨ hsame row semigroupRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont B A graphRead ∧
                      Cont graphRead R resolventRead ∧
                        Cont resolventRead S semigroupRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle L pkg)
                  hsame ∧
                UnaryHistory graphRead ∧ UnaryHistory resolventRead ∧
                  UnaryHistory semigroupRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro bUnary aUnary rUnary sUnary _nUnary _cUnary graphRoute resolventRoute
    semigroupRoute _replayRoute provenancePkg localNamePkg
  have graphUnary : UnaryHistory graphRead :=
    unary_cont_closed bUnary aUnary graphRoute
  have resolventUnary : UnaryHistory resolventRead :=
    unary_cont_closed graphUnary rUnary resolventRoute
  have semigroupUnary : UnaryHistory semigroupRead :=
    unary_cont_closed resolventUnary sUnary semigroupRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row semigroupRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row A ∨ hsame row R ∨ hsame row S ∨ hsame row N ∨
              hsame row semigroupRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B A graphRead ∧ Cont graphRead R resolventRead ∧
              Cont resolventRead S semigroupRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle L pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro semigroupRead ⟨hsame_refl semigroupRead, semigroupUnary⟩
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
      exact
        ⟨source.right, graphRoute, resolventRoute, semigroupRoute, provenancePkg,
          localNamePkg⟩
  }
  exact ⟨cert, graphUnary, resolventUnary, semigroupUnary⟩

end BEDC.Derived.HilleYosidaUp
