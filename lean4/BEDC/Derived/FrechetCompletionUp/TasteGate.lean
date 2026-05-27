import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FrechetCompletionUp

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

inductive FrechetCompletionUp : Type where
  | mk (A L N S Q R H C P K : BHist) : FrechetCompletionUp
  deriving DecidableEq

def frechetCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: frechetCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: frechetCompletionEncodeBHist h

def frechetCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (frechetCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (frechetCompletionDecodeBHist tail)

private theorem frechetCompletion_decode_encode :
    ∀ h : BHist, frechetCompletionDecodeBHist (frechetCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def frechetCompletionFields : FrechetCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FrechetCompletionUp.mk A L N S Q R H C P K => [A, L, N, S, Q, R, H, C, P, K]

def frechetCompletionToEventFlow : FrechetCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (frechetCompletionFields x).map frechetCompletionEncodeBHist

private def frechetCompletionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => frechetCompletionEventAt index rest

def frechetCompletionFromEventFlow (ef : EventFlow) : Option FrechetCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FrechetCompletionUp.mk
      (frechetCompletionDecodeBHist (frechetCompletionEventAt 0 ef))
      (frechetCompletionDecodeBHist (frechetCompletionEventAt 1 ef))
      (frechetCompletionDecodeBHist (frechetCompletionEventAt 2 ef))
      (frechetCompletionDecodeBHist (frechetCompletionEventAt 3 ef))
      (frechetCompletionDecodeBHist (frechetCompletionEventAt 4 ef))
      (frechetCompletionDecodeBHist (frechetCompletionEventAt 5 ef))
      (frechetCompletionDecodeBHist (frechetCompletionEventAt 6 ef))
      (frechetCompletionDecodeBHist (frechetCompletionEventAt 7 ef))
      (frechetCompletionDecodeBHist (frechetCompletionEventAt 8 ef))
      (frechetCompletionDecodeBHist (frechetCompletionEventAt 9 ef)))

private theorem frechetCompletion_round_trip (x : FrechetCompletionUp) :
    frechetCompletionFromEventFlow (frechetCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A L N S Q R H C P K =>
      change
        some
          (FrechetCompletionUp.mk
            (frechetCompletionDecodeBHist (frechetCompletionEncodeBHist A))
            (frechetCompletionDecodeBHist (frechetCompletionEncodeBHist L))
            (frechetCompletionDecodeBHist (frechetCompletionEncodeBHist N))
            (frechetCompletionDecodeBHist (frechetCompletionEncodeBHist S))
            (frechetCompletionDecodeBHist (frechetCompletionEncodeBHist Q))
            (frechetCompletionDecodeBHist (frechetCompletionEncodeBHist R))
            (frechetCompletionDecodeBHist (frechetCompletionEncodeBHist H))
            (frechetCompletionDecodeBHist (frechetCompletionEncodeBHist C))
            (frechetCompletionDecodeBHist (frechetCompletionEncodeBHist P))
            (frechetCompletionDecodeBHist (frechetCompletionEncodeBHist K))) =
          some (FrechetCompletionUp.mk A L N S Q R H C P K)
      rw [frechetCompletion_decode_encode A, frechetCompletion_decode_encode L,
        frechetCompletion_decode_encode N, frechetCompletion_decode_encode S,
        frechetCompletion_decode_encode Q, frechetCompletion_decode_encode R,
        frechetCompletion_decode_encode H, frechetCompletion_decode_encode C,
        frechetCompletion_decode_encode P, frechetCompletion_decode_encode K]

private theorem frechetCompletionToEventFlow_injective {x y : FrechetCompletionUp} :
    frechetCompletionToEventFlow x = frechetCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      frechetCompletionFromEventFlow (frechetCompletionToEventFlow x) =
        frechetCompletionFromEventFlow (frechetCompletionToEventFlow y) :=
    congrArg frechetCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (frechetCompletion_round_trip x).symm
      (Eq.trans hread (frechetCompletion_round_trip y)))

instance frechetCompletionBHistCarrier : BHistCarrier FrechetCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := frechetCompletionToEventFlow
  fromEventFlow := frechetCompletionFromEventFlow

instance frechetCompletionChapterTasteGate : ChapterTasteGate FrechetCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change frechetCompletionFromEventFlow (frechetCompletionToEventFlow x) = some x
    exact frechetCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (frechetCompletionToEventFlow_injective heq)

theorem FrechetCompletionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {A L N S Q R H C P K filterRead netRead completionRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont A L filterRead →
      Cont filterRead N netRead →
        Cont N S completionRead →
          Cont Q R sealRead →
            PkgSig bundle P pkg →
              PkgSig bundle K pkg →
                UnaryHistory A →
                  UnaryHistory L →
                    UnaryHistory N →
                      UnaryHistory S →
                        UnaryHistory Q →
                          UnaryHistory R →
                            UnaryHistory K →
                              SemanticNameCert
                                  (fun row : BHist =>
                                    hsame row filterRead ∨ hsame row netRead ∨
                                      hsame row completionRead ∨ hsame row sealRead ∨
                                        hsame row K)
                                  (fun row : BHist => UnaryHistory row)
                                  (fun row : BHist =>
                                    PkgSig bundle P pkg ∨ PkgSig bundle row pkg)
                                  hsame ∧
                                Nonempty (ChapterTasteGate FrechetCompletionUp) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro filterRoute netRoute completionRoute sealRoute packageP packageK unaryA unaryL unaryN
    unaryS unaryQ unaryR unaryK
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed unaryA unaryL filterRoute
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed filterUnary unaryN netRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed unaryN unaryS completionRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed unaryQ unaryR sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row filterRead ∨ hsame row netRead ∨ hsame row completionRead ∨
              hsame row sealRead ∨ hsame row K)
          (fun row : BHist => UnaryHistory row)
          (fun row : BHist => PkgSig bundle P pkg ∨ PkgSig bundle row pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro filterRead (Or.inl (hsame_refl filterRead))
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
        cases source with
        | inl sameFilter =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameFilter)
        | inr rest =>
            cases rest with
            | inl sameNet =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameNet))
            | inr rest =>
                cases rest with
                | inl sameCompletion =>
                    exact Or.inr
                      (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameCompletion)))
                | inr rest =>
                    cases rest with
                    | inl sameSeal =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inl (hsame_trans (hsame_symm sameRows) sameSeal))))
                    | inr sameK =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (hsame_trans (hsame_symm sameRows) sameK))))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameFilter =>
          exact unary_transport filterUnary (hsame_symm sameFilter)
      | inr rest =>
          cases rest with
          | inl sameNet =>
              exact unary_transport netUnary (hsame_symm sameNet)
          | inr rest =>
              cases rest with
              | inl sameCompletion =>
                  exact unary_transport completionUnary (hsame_symm sameCompletion)
              | inr rest =>
                  cases rest with
                  | inl sameSeal =>
                      exact unary_transport sealUnary (hsame_symm sameSeal)
                  | inr sameK =>
                      exact unary_transport unaryK (hsame_symm sameK)
    ledger_sound := by
      intro _row source
      cases source with
      | inl _sameFilter =>
          exact Or.inl packageP
      | inr rest =>
          cases rest with
          | inl _sameNet =>
              exact Or.inl packageP
          | inr rest =>
              cases rest with
              | inl _sameCompletion =>
                  exact Or.inl packageP
              | inr rest =>
                  cases rest with
                  | inl _sameSeal =>
                      exact Or.inl packageP
                  | inr sameK =>
                      cases sameK
                      exact Or.inr packageK
  }
  exact ⟨cert, ⟨frechetCompletionChapterTasteGate⟩⟩

end BEDC.Derived.FrechetCompletionUp
