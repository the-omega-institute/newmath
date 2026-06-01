import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EpigraphUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EpigraphCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {D V L O H C P N valueRead lowerRead epigraphRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont D V valueRead ->
      Cont valueRead L lowerRead ->
        Cont lowerRead O epigraphRead ->
          PkgSig bundle P pkg ->
            UnaryHistory D ->
              UnaryHistory V ->
                UnaryHistory L ->
                  UnaryHistory O ->
                    SemanticNameCert
                        (fun row : BHist => hsame row epigraphRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row D ∨ hsame row V ∨ hsame row L ∨ hsame row O ∨
                            hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                              hsame row valueRead ∨ hsame row lowerRead ∨
                                hsame row epigraphRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont D V valueRead ∧
                            Cont valueRead L lowerRead ∧ Cont lowerRead O epigraphRead ∧
                              PkgSig bundle P pkg)
                        hsame ∧
                      UnaryHistory valueRead ∧ UnaryHistory lowerRead ∧
                        UnaryHistory epigraphRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro valueRoute lowerRoute epigraphRoute pkgP unaryD unaryV unaryL unaryO
  have valueUnary : UnaryHistory valueRead :=
    unary_cont_closed unaryD unaryV valueRoute
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed valueUnary unaryL lowerRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed lowerUnary unaryO epigraphRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row epigraphRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row V ∨ hsame row L ∨ hsame row O ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row valueRead ∨
                hsame row lowerRead ∨ hsame row epigraphRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D V valueRead ∧ Cont valueRead L lowerRead ∧
              Cont lowerRead O epigraphRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro epigraphRead ⟨hsame_refl epigraphRead, epigraphUnary⟩
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
                      (Or.inr
                        (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, valueRoute, lowerRoute, epigraphRoute, pkgP⟩
  }
  exact ⟨cert, valueUnary, lowerUnary, epigraphUnary⟩

end BEDC.Derived.EpigraphUp
