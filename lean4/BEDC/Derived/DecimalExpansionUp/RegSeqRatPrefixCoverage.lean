import BEDC.Derived.DecimalExpansionUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DecimalExpansionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DecimalExpansionRegSeqRatPrefixCoverage
    {D W V Q R E H C P N prefixRead placeRead dyadicRead regseqRead realSeal :
      BHist} :
    UnaryHistory D ->
      UnaryHistory W ->
        UnaryHistory V ->
          UnaryHistory Q ->
            UnaryHistory R ->
              UnaryHistory E ->
                Cont D W prefixRead ->
                  Cont prefixRead V placeRead ->
                    Cont placeRead Q dyadicRead ->
                      Cont dyadicRead R regseqRead ->
                        Cont regseqRead E realSeal ->
                          UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory prefixRead ∧
                            UnaryHistory placeRead ∧ UnaryHistory dyadicRead ∧
                              UnaryHistory regseqRead ∧ UnaryHistory realSeal ∧
                                hsame regseqRead (append dyadicRead R) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro dUnary wUnary vUnary qUnary rUnary eUnary digitWindow prefixPlace
    placeDyadic dyadicRegSeq regSeqSeal
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed dUnary wUnary digitWindow
  have placeUnary : UnaryHistory placeRead :=
    unary_cont_closed prefixUnary vUnary prefixPlace
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed placeUnary qUnary placeDyadic
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed dyadicUnary rUnary dyadicRegSeq
  have sealUnary : UnaryHistory realSeal :=
    unary_cont_closed regseqUnary eUnary regSeqSeal
  exact
    ⟨dUnary, wUnary, prefixUnary, placeUnary, dyadicUnary, regseqUnary, sealUnary,
      dyadicRegSeq⟩

end BEDC.Derived.DecimalExpansionUp
