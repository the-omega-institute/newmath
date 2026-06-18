import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DecidableBarUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DecidableBarCarrier (C S W R D H T P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame Pkg NameCert UnaryHistory
  UnaryHistory C ∧ UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory R ∧
    UnaryHistory D ∧ UnaryHistory H ∧ UnaryHistory T ∧ UnaryHistory P ∧
      UnaryHistory N ∧ hsame H (append C S) ∧ Cont C S W ∧ Cont W R D

theorem DecidableBarCarrier_stream_window_route
    {C S W R D H T P N streamWindow barWindow depthRead : BHist} :
    DecidableBarCarrier C S W R D H T P N ->
      Cont C S streamWindow ->
        Cont streamWindow W barWindow ->
          Cont barWindow R depthRead ->
            UnaryHistory streamWindow ∧ UnaryHistory barWindow ∧
              UnaryHistory depthRead ∧ hsame H (append C S) ∧
                Cont C S streamWindow ∧ Cont streamWindow W barWindow ∧
                  Cont barWindow R depthRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame Pkg NameCert UnaryHistory DecidableBarCarrier
  intro carrier streamRoute barRoute depthRoute
  obtain
    ⟨unaryC, unaryS, unaryW, unaryR, _unaryD, _unaryH, _unaryT, _unaryP,
      _unaryN, sameH, _carrierStreamRoute, _carrierDepthRoute⟩ := carrier
  have streamUnary : UnaryHistory streamWindow :=
    unary_cont_closed unaryC unaryS streamRoute
  have barUnary : UnaryHistory barWindow :=
    unary_cont_closed streamUnary unaryW barRoute
  have depthUnary : UnaryHistory depthRead :=
    unary_cont_closed barUnary unaryR depthRoute
  exact ⟨streamUnary, barUnary, depthUnary, sameH, streamRoute, barRoute, depthRoute⟩

theorem DecidableBarCarrier_namecert_obligations
    {C S W R D H T P N depthRead nameRead : BHist} :
    DecidableBarCarrier C S W R D H T P N →
      Cont W R depthRead →
        Cont P N nameRead →
          SemanticNameCert
              (fun row : BHist =>
                (hsame row C ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨
                    hsame row D ∨ hsame row H ∨ hsame row T ∨ hsame row P ∨
                      hsame row N ∨ hsame row nameRead) ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row C ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨
                  hsame row D ∨ hsame row H ∨ hsame row T ∨ hsame row P ∨
                    hsame row N ∨ hsame row nameRead)
              (fun row : BHist =>
                UnaryHistory row ∧
                  (hsame row C ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨
                    hsame row D ∨ hsame row H ∨ hsame row T ∨ hsame row P ∨
                      hsame row N ∨ hsame row nameRead))
              hsame ∧
            UnaryHistory depthRead ∧ UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: DecidableBarCarrier BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier depthRoute nameRoute
  obtain
    ⟨unaryC, unaryS, unaryW, unaryR, unaryD, unaryH, unaryT, unaryP, unaryN,
      _sameH, _carrierStreamRoute, _carrierDepthRoute⟩ := carrier
  have depthUnary : UnaryHistory depthRead :=
    unary_cont_closed unaryW unaryR depthRoute
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed unaryP unaryN nameRoute
  have nameSource :
      (fun row : BHist =>
        (hsame row C ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
            hsame row H ∨ hsame row T ∨ hsame row P ∨ hsame row N ∨
              hsame row nameRead) ∧ UnaryHistory row) nameRead := by
    exact
      ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (hsame_refl nameRead))))))))), nameUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row C ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
                hsame row H ∨ hsame row T ∨ hsame row P ∨ hsame row N ∨
                  hsame row nameRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
              hsame row H ∨ hsame row T ∨ hsame row P ∨ hsame row N ∨
                hsame row nameRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              (hsame row C ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨
                hsame row D ∨ hsame row H ∨ hsame row T ∨ hsame row P ∨
                  hsame row N ∨ hsame row nameRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nameRead nameSource
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, source.left⟩
  }
  exact ⟨cert, depthUnary, nameUnary⟩

end BEDC.Derived.DecidableBarUp
