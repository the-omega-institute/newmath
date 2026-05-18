import BEDC.Derived.AuthorizedGeneratorRecursorUp.TasteGate

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorUp_structural_descent_locality
    {signature eliminator motive branches descent output audit transport routes provenance gap name
      descentRead outputRead : BHist} :
    UnaryHistory descent →
      UnaryHistory routes →
        UnaryHistory output →
          Cont descent routes descentRead →
            Cont descentRead output outputRead →
              hsame descent descent ∧
                hsame output output ∧
                  UnaryHistory descentRead ∧
                    UnaryHistory outputRead ∧
                      Cont descent routes descentRead ∧
                        Cont descentRead output outputRead ∧
                          (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches
                              descent output audit transport routes provenance gap name =
                            AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches
                              descent output audit transport routes provenance gap name) := by
  -- BEDC touchpoint anchor: BHist AuthorizedGeneratorRecursorUp hsame Cont UnaryHistory
  intro descentUnary routesUnary outputUnary descentRoutesRead descentReadOutputRead
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed descentUnary routesUnary descentRoutesRead
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed descentReadUnary outputUnary descentReadOutputRead
  exact
    ⟨hsame_refl descent, hsame_refl output, descentReadUnary, outputReadUnary,
      descentRoutesRead, descentReadOutputRead, rfl⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
