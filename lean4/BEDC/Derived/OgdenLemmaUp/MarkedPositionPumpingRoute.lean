import BEDC.Derived.OgdenLemmaUp.NameCertObligations

namespace BEDC.Derived.OgdenLemmaUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem OgdenLemmaCarrier_marked_position_pumping_route [AskSetup] [PackageSetup]
    {G W M D A E I Y _H _C R _Q N derivationRead decompositionRead pumpedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory G ->
      UnaryHistory W ->
        UnaryHistory M ->
          UnaryHistory D ->
            UnaryHistory A ->
              UnaryHistory E ->
                UnaryHistory I ->
                  UnaryHistory Y ->
                    Cont G W derivationRead ->
                      Cont M D decompositionRead ->
                        Cont E I pumpedRead ->
                          PkgSig bundle N pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row pumpedRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row G ∨ hsame row W ∨ hsame row M ∨
                                    hsame row D ∨ hsame row A ∨ hsame row E ∨
                                      hsame row I ∨ hsame row Y ∨ hsame row R ∨
                                        hsame row pumpedRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont G W derivationRead ∧
                                    Cont M D decompositionRead ∧ Cont E I pumpedRead ∧
                                      PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory derivationRead ∧
                                UnaryHistory decompositionRead ∧ UnaryHistory pumpedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro unaryG unaryW unaryM unaryD _unaryA unaryE unaryI _unaryY derivationRoute
    decompositionRoute pumpedRoute pkgN
  have derivationUnary : UnaryHistory derivationRead :=
    unary_cont_closed unaryG unaryW derivationRoute
  have decompositionUnary : UnaryHistory decompositionRead :=
    unary_cont_closed unaryM unaryD decompositionRoute
  have pumpedUnary : UnaryHistory pumpedRead :=
    unary_cont_closed unaryE unaryI pumpedRoute
  have sourceAtPumped : hsame pumpedRead pumpedRead ∧ UnaryHistory pumpedRead :=
    ⟨hsame_refl pumpedRead, pumpedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row pumpedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row G ∨ hsame row W ∨ hsame row M ∨ hsame row D ∨ hsame row A ∨
              hsame row E ∨ hsame row I ∨ hsame row Y ∨ hsame row R ∨ hsame row pumpedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont G W derivationRead ∧ Cont M D decompositionRead ∧
              Cont E I pumpedRead ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro pumpedRead sourceAtPumped
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
      right; right; right; right; right; right; right; right; right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, derivationRoute, decompositionRoute, pumpedRoute, pkgN⟩
  }
  exact ⟨cert, derivationUnary, decompositionUnary, pumpedUnary⟩

end BEDC.Derived.OgdenLemmaUp
