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

namespace BEDC.Derived.BishopChainConnectedUp

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

inductive BishopChainConnectedUp : Type where
  | mk (I A Z D J W R Q H C P N : BHist) : BishopChainConnectedUp
  deriving DecidableEq

def bishopChainConnectedEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopChainConnectedEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopChainConnectedEncodeBHist h

def bishopChainConnectedDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopChainConnectedDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopChainConnectedDecodeBHist tail)

private theorem BishopChainConnectedTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopChainConnectedFields : BishopChainConnectedUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopChainConnectedUp.mk I A Z D J W R Q H C P N => [I, A, Z, D, J, W, R, Q, H, C, P, N]

def bishopChainConnectedToEventFlow : BishopChainConnectedUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopChainConnectedFields x).map bishopChainConnectedEncodeBHist

private def bishopChainConnectedEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopChainConnectedEventAt index rest

def bishopChainConnectedFromEventFlow (ef : EventFlow) :
    Option BishopChainConnectedUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopChainConnectedUp.mk
      (bishopChainConnectedDecodeBHist (bishopChainConnectedEventAt 0 ef))
      (bishopChainConnectedDecodeBHist (bishopChainConnectedEventAt 1 ef))
      (bishopChainConnectedDecodeBHist (bishopChainConnectedEventAt 2 ef))
      (bishopChainConnectedDecodeBHist (bishopChainConnectedEventAt 3 ef))
      (bishopChainConnectedDecodeBHist (bishopChainConnectedEventAt 4 ef))
      (bishopChainConnectedDecodeBHist (bishopChainConnectedEventAt 5 ef))
      (bishopChainConnectedDecodeBHist (bishopChainConnectedEventAt 6 ef))
      (bishopChainConnectedDecodeBHist (bishopChainConnectedEventAt 7 ef))
      (bishopChainConnectedDecodeBHist (bishopChainConnectedEventAt 8 ef))
      (bishopChainConnectedDecodeBHist (bishopChainConnectedEventAt 9 ef))
      (bishopChainConnectedDecodeBHist (bishopChainConnectedEventAt 10 ef))
      (bishopChainConnectedDecodeBHist (bishopChainConnectedEventAt 11 ef)))

private theorem BishopChainConnectedTasteGate_single_carrier_alignment_round_trip
    (x : BishopChainConnectedUp) :
    bishopChainConnectedFromEventFlow (bishopChainConnectedToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I A Z D J W R Q H C P N =>
      change
        some
          (BishopChainConnectedUp.mk
            (bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist I))
            (bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist A))
            (bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist Z))
            (bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist D))
            (bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist J))
            (bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist W))
            (bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist R))
            (bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist Q))
            (bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist H))
            (bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist C))
            (bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist P))
            (bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist N))) =
          some (BishopChainConnectedUp.mk I A Z D J W R Q H C P N)
      rw [BishopChainConnectedTasteGate_single_carrier_alignment_decode_encode I,
        BishopChainConnectedTasteGate_single_carrier_alignment_decode_encode A,
        BishopChainConnectedTasteGate_single_carrier_alignment_decode_encode Z,
        BishopChainConnectedTasteGate_single_carrier_alignment_decode_encode D,
        BishopChainConnectedTasteGate_single_carrier_alignment_decode_encode J,
        BishopChainConnectedTasteGate_single_carrier_alignment_decode_encode W,
        BishopChainConnectedTasteGate_single_carrier_alignment_decode_encode R,
        BishopChainConnectedTasteGate_single_carrier_alignment_decode_encode Q,
        BishopChainConnectedTasteGate_single_carrier_alignment_decode_encode H,
        BishopChainConnectedTasteGate_single_carrier_alignment_decode_encode C,
        BishopChainConnectedTasteGate_single_carrier_alignment_decode_encode P,
        BishopChainConnectedTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopChainConnectedTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopChainConnectedUp} :
    bishopChainConnectedToEventFlow x = bishopChainConnectedToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopChainConnectedFromEventFlow (bishopChainConnectedToEventFlow x) =
        bishopChainConnectedFromEventFlow (bishopChainConnectedToEventFlow y) :=
    congrArg bishopChainConnectedFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopChainConnectedTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopChainConnectedTasteGate_single_carrier_alignment_round_trip y)))

instance bishopChainConnectedBHistCarrier : BHistCarrier BishopChainConnectedUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopChainConnectedToEventFlow
  fromEventFlow := bishopChainConnectedFromEventFlow

instance bishopChainConnectedChapterTasteGate :
    ChapterTasteGate BishopChainConnectedUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopChainConnectedFromEventFlow (bishopChainConnectedToEventFlow x) = some x
    exact BishopChainConnectedTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopChainConnectedTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def BishopChainConnectedCarrier [AskSetup] [PackageSetup]
    (I A Z D J W R Q H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory I ∧ UnaryHistory A ∧ UnaryHistory Z ∧ UnaryHistory D ∧
    UnaryHistory J ∧ UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory Q ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem BishopChainConnectedCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {I A Z D J W R Q H C P N chainRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopChainConnectedCarrier I A Z D J W R Q H C P N bundle pkg ->
      Cont Z D chainRead ->
        Cont chainRead Q sealRead ->
          PkgSig bundle sealRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row I ∨ hsame row A ∨ hsame row Z ∨ hsame row D ∨
                    hsame row J ∨ hsame row W ∨ hsame row R ∨ hsame row Q ∨
                      hsame row chainRead ∨ hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont Z D chainRead ∧ Cont chainRead Q sealRead ∧
                    PkgSig bundle sealRead pkg)
                hsame ∧
              UnaryHistory chainRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier chainRoute sealRoute sealPkg
  obtain ⟨_iUnary, _aUnary, zUnary, dUnary, _jUnary, _wUnary, _rUnary, qUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _provenancePkg, _localNamePkg⟩ := carrier
  have chainReadUnary : UnaryHistory chainRead :=
    unary_cont_closed zUnary dUnary chainRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed chainReadUnary qUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row A ∨ hsame row Z ∨ hsame row D ∨ hsame row J ∨
              hsame row W ∨ hsame row R ∨ hsame row Q ∨ hsame row chainRead ∨
                hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z D chainRead ∧ Cont chainRead Q sealRead ∧
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, chainRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, chainReadUnary, sealReadUnary⟩

end BEDC.Derived.BishopChainConnectedUp
