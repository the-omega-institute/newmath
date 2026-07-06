import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.OgdenLemmaUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem OgdenLemmaCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {G W M D A E I Y H C R Q N nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory G ->
      UnaryHistory W ->
        UnaryHistory M ->
          UnaryHistory D ->
            UnaryHistory A ->
              UnaryHistory E ->
                UnaryHistory I ->
                  UnaryHistory Y ->
                    UnaryHistory H ->
                      UnaryHistory C ->
                        UnaryHistory R ->
                          UnaryHistory Q ->
                            UnaryHistory N ->
                              Cont G W M ->
                                Cont M D A ->
                                  Cont A E I ->
                                    Cont I Y C ->
                                      Cont C R nameRead ->
                                        PkgSig bundle Q pkg ->
                                          SemanticNameCert
                                              (fun row : BHist =>
                                                hsame row nameRead ∧ UnaryHistory row)
                                              (fun row : BHist =>
                                                hsame row G ∨ hsame row W ∨ hsame row M ∨
                                                  hsame row D ∨ hsame row A ∨ hsame row E ∨
                                                    hsame row I ∨ hsame row Y ∨ hsame row H ∨
                                                      hsame row C ∨ hsame row R ∨
                                                        hsame row Q ∨ hsame row N ∨
                                                          hsame row nameRead)
                                              (fun row : BHist =>
                                                UnaryHistory row ∧ Cont G W M ∧
                                                  Cont M D A ∧ Cont A E I ∧ Cont I Y C ∧
                                                    Cont C R nameRead ∧ PkgSig bundle Q pkg)
                                              hsame ∧
                                            UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro unaryG unaryW unaryM unaryD unaryA unaryE unaryI unaryY _unaryH unaryC unaryR
    _unaryQ _unaryN routeM routeA routeI routeC routeName pkgQ
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed unaryC unaryR routeName
  have sourceAtName : hsame nameRead nameRead ∧ UnaryHistory nameRead :=
    ⟨hsame_refl nameRead, nameUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row G ∨ hsame row W ∨ hsame row M ∨ hsame row D ∨ hsame row A ∨
              hsame row E ∨ hsame row I ∨ hsame row Y ∨ hsame row H ∨ hsame row C ∨
                hsame row R ∨ hsame row Q ∨ hsame row N ∨ hsame row nameRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont G W M ∧ Cont M D A ∧ Cont A E I ∧ Cont I Y C ∧
              Cont C R nameRead ∧ PkgSig bundle Q pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nameRead sourceAtName
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
      intro row source
      right; right; right; right; right; right; right; right; right; right; right; right
      right
      exact source.left
    ledger_sound := by
      intro row source
      exact ⟨source.right, routeM, routeA, routeI, routeC, routeName, pkgQ⟩
  }
  exact ⟨cert, nameUnary⟩

end BEDC.Derived.OgdenLemmaUp
