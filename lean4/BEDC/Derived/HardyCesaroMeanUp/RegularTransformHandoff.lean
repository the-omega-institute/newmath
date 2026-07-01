import BEDC.Derived.HardyCesaroMeanUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HardyCesaroMeanUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HardyCesaroMeanRegularTransformHandoff [AskSetup] [PackageSetup]
    {S P U D R E T C Q N transformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S ->
      UnaryHistory P ->
        UnaryHistory U ->
          UnaryHistory D ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory T ->
                  UnaryHistory C ->
                    UnaryHistory Q ->
                      UnaryHistory N ->
                        Cont S P U ->
                          Cont U D R ->
                            Cont R E transformRead ->
                              PkgSig bundle Q pkg ->
                                PkgSig bundle N pkg ->
                                  PkgSig bundle transformRead pkg ->
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row transformRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row S ∨ hsame row P ∨ hsame row U ∨
                                            hsame row D ∨ hsame row R ∨ hsame row E ∨
                                              hsame row T ∨ hsame row C ∨
                                                hsame row Q ∨ hsame row N ∨
                                                  hsame row transformRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont S P U ∧
                                            Cont U D R ∧ Cont R E transformRead ∧
                                              PkgSig bundle transformRead pkg)
                                        hsame ∧ UnaryHistory transformRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro sUnary pUnary uUnary dUnary rUnary eUnary _tUnary _cUnary _qUnary _nUnary
    sourceRoute denominatorRoute transformRoute _qPkg _nPkg transformPkg
  have sourceUnary : UnaryHistory U :=
    unary_cont_closed sUnary pUnary sourceRoute
  have readbackUnary : UnaryHistory R :=
    unary_cont_closed sourceUnary dUnary denominatorRoute
  have transformUnary : UnaryHistory transformRead :=
    unary_cont_closed readbackUnary eUnary transformRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row transformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row P ∨ hsame row U ∨ hsame row D ∨ hsame row R ∨
              hsame row E ∨ hsame row T ∨ hsame row C ∨ hsame row Q ∨ hsame row N ∨
                hsame row transformRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S P U ∧ Cont U D R ∧ Cont R E transformRead ∧
              PkgSig bundle transformRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro transformRead
        ⟨hsame_refl transformRead, transformUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceRoute, denominatorRoute, transformRoute, transformPkg⟩
  }
  exact ⟨cert, transformUnary⟩

end BEDC.Derived.HardyCesaroMeanUp
