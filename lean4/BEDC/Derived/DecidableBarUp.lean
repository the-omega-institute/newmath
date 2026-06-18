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

end BEDC.Derived.DecidableBarUp
