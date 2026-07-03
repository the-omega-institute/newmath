import BEDC.Derived.BoundedRegularCauchyUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BoundedRegularCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedRegularCauchyCarrier_real_seal_boundary [AskSetup] [PackageSetup]
    {S M B Q A modulusRead windowRead boundRead readbackRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S ->
      UnaryHistory M ->
        UnaryHistory B ->
          UnaryHistory Q ->
            UnaryHistory A ->
              Cont M S modulusRead ->
                Cont modulusRead B windowRead ->
                  Cont windowRead Q boundRead ->
                    Cont boundRead A readbackRead ->
                      PkgSig bundle readbackRead pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row readbackRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row S ∨ hsame row M ∨ hsame row B ∨ hsame row Q ∨
                                hsame row A ∨ hsame row readbackRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont M S modulusRead ∧
                                Cont modulusRead B windowRead ∧ Cont windowRead Q boundRead ∧
                                  Cont boundRead A readbackRead ∧
                                    PkgSig bundle readbackRead pkg)
                            hsame ∧
                          UnaryHistory modulusRead ∧ UnaryHistory windowRead ∧
                            UnaryHistory boundRead ∧ UnaryHistory readbackRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro sUnary mUnary bUnary qUnary aUnary modulusRoute windowRoute boundRoute readbackRoute
    readbackPkg
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed mUnary sUnary modulusRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed modulusUnary bUnary windowRoute
  have boundUnary : UnaryHistory boundRead :=
    unary_cont_closed windowUnary qUnary boundRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed boundUnary aUnary readbackRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readbackRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row M ∨ hsame row B ∨ hsame row Q ∨ hsame row A ∨
              hsame row readbackRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M S modulusRead ∧ Cont modulusRead B windowRead ∧
              Cont windowRead Q boundRead ∧ Cont boundRead A readbackRead ∧
                PkgSig bundle readbackRead pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨readbackRead, hsame_refl readbackRead, readbackUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, modulusRoute, windowRoute, boundRoute, readbackRoute, readbackPkg⟩
  }
  exact ⟨cert, modulusUnary, windowUnary, boundUnary, readbackUnary⟩

end BEDC.Derived.BoundedRegularCauchyUp
