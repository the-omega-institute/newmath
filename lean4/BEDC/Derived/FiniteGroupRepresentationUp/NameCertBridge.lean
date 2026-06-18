import BEDC.Derived.FiniteGroupRepresentationUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteGroupRepresentationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteGroupRepresentationNameCertBridge [AskSetup] [PackageSetup]
    {G V L M A U C H P N actionRead unitRead consumerRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont G A actionRead ->
      Cont U A unitRead ->
        Cont actionRead C consumerRead ->
          Cont H N namedRead ->
            UnaryHistory G ->
              UnaryHistory V ->
                UnaryHistory L ->
                  UnaryHistory M ->
                    UnaryHistory A ->
                      UnaryHistory U ->
                        UnaryHistory C ->
                          UnaryHistory H ->
                            UnaryHistory N ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row C ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row G ∨ hsame row V ∨ hsame row L ∨
                                          hsame row M ∨ hsame row A ∨ hsame row U ∨
                                            hsame row C ∨ hsame row H ∨ hsame row P ∨
                                              hsame row N)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                          PkgSig bundle N pkg)
                                      hsame ∧ UnaryHistory actionRead ∧
                                        UnaryHistory unitRead ∧ UnaryHistory consumerRead ∧
                                          UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert ProbeBundle Pkg PkgSig
  intro actionRoute unitRoute consumerRoute namedRoute GUnary VUnary LUnary MUnary AUnary
    UUnary CUnary HUnary NUnary provenancePkg namePkg
  have actionUnary : UnaryHistory actionRead :=
    unary_cont_closed GUnary AUnary actionRoute
  have unitUnary : UnaryHistory unitRead :=
    unary_cont_closed UUnary AUnary unitRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed actionUnary CUnary consumerRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed HUnary NUnary namedRoute
  have sourceAtConsumerRow : hsame C C ∧ UnaryHistory C :=
    ⟨hsame_refl C, CUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row C ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row G ∨ hsame row V ∨ hsame row L ∨ hsame row M ∨ hsame row A ∨
              hsame row U ∨ hsame row C ∨ hsame row H ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro C sourceAtConsumerRow
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
      cases source.left
      right
      right
      right
      right
      right
      right
      left
      exact hsame_refl C
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namePkg⟩
  }
  exact ⟨cert, actionUnary, unitUnary, consumerUnary, namedUnary⟩

end BEDC.Derived.FiniteGroupRepresentationUp
