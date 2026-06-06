import BEDC.Derived.RegularCauchyReciprocalUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyReciprocalUp.TasteGate

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyReciprocalTailStability [AskSetup] [PackageSetup]
    {Q A M W D B T E H C P N laterWindow reciprocalRead budgetRead terminalRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory Q ->
      UnaryHistory A ->
        UnaryHistory M ->
          UnaryHistory W ->
            UnaryHistory D ->
              UnaryHistory B ->
                UnaryHistory T ->
                  UnaryHistory E ->
                    UnaryHistory N ->
                      Cont Q A laterWindow ->
                        Cont laterWindow W reciprocalRead ->
                          Cont reciprocalRead D budgetRead ->
                            Cont budgetRead T terminalRead ->
                              Cont terminalRead E namedRead ->
                                hsame H (append C P) ->
                                  PkgSig bundle P pkg ->
                                    PkgSig bundle N pkg ->
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row namedRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row Q ∨ hsame row A ∨
                                              hsame row M ∨ hsame row W ∨
                                                hsame row D ∨ hsame row B ∨
                                                  hsame row T ∨ hsame row E ∨
                                                    hsame row namedRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧
                                              Cont Q A laterWindow ∧
                                                Cont laterWindow W reciprocalRead ∧
                                                  Cont reciprocalRead D budgetRead ∧
                                                    Cont budgetRead T terminalRead ∧
                                                      Cont terminalRead E namedRead ∧
                                                        hsame H (append C P) ∧
                                                          PkgSig bundle P pkg ∧
                                                            PkgSig bundle N pkg)
                                          hsame ∧ UnaryHistory laterWindow ∧
                                        UnaryHistory reciprocalRead ∧
                                          UnaryHistory budgetRead ∧
                                            UnaryHistory terminalRead ∧
                                              UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert append
  intro qUnary aUnary _mUnary wUnary dUnary _bUnary tUnary eUnary _nUnary laterRoute
    reciprocalRoute budgetRoute terminalRoute namedRoute appendAnchor provenancePkg namePkg
  have laterUnary : UnaryHistory laterWindow :=
    unary_cont_closed qUnary aUnary laterRoute
  have reciprocalUnary : UnaryHistory reciprocalRead :=
    unary_cont_closed laterUnary wUnary reciprocalRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed reciprocalUnary dUnary budgetRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed budgetUnary tUnary terminalRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed terminalUnary eUnary namedRoute
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
                        (Or.inr source.left)))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, laterRoute, reciprocalRoute, budgetRoute, terminalRoute,
            namedRoute, appendAnchor, provenancePkg, namePkg⟩
    }
  · exact
      ⟨laterUnary, reciprocalUnary, budgetUnary, terminalUnary, namedUnary⟩

end BEDC.Derived.RegularCauchyReciprocalUp.TasteGate
