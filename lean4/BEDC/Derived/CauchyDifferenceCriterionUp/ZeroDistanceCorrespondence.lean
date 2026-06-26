import BEDC.Derived.CauchyDifferenceCriterionUp.TailDiameterHandoff
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyDifferenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyDifferenceCriterionZeroDistanceCorrespondence [AskSetup] [PackageSetup]
    {X Y D Z Q W T E H C P N diffRead nullRead zeroRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    cauchyDifferenceCriterionFields (CauchyDifferenceCriterionUp.mk X Y D Z Q W T E H C P N) =
        [X, Y, D, Z, Q, W, T, E, H, C, P, N] ->
      UnaryHistory D ->
        UnaryHistory Z ->
          UnaryHistory Q ->
            UnaryHistory E ->
              Cont D Z nullRead ->
                Cont nullRead Q zeroRead ->
                  Cont zeroRead E sealRead ->
                    PkgSig bundle P pkg ->
                      PkgSig bundle N pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row D ∨ hsame row Z ∨ hsame row Q ∨ hsame row E ∨
                                Cont zeroRead E sealRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont D Z nullRead ∧
                                Cont nullRead Q zeroRead ∧ Cont zeroRead E sealRead ∧
                                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                            hsame ∧
                          UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: CauchyDifferenceCriterionUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fields dUnary zUnary qUnary eUnary nullRoute zeroRoute sealRoute pPkg nPkg
  have _acceptedFields :
      cauchyDifferenceCriterionFields (CauchyDifferenceCriterionUp.mk X Y D Z Q W T E H C P N) =
        [X, Y, D, Z, Q, W, T, E, H, C, P, N] := fields
  have nullUnary : UnaryHistory nullRead :=
    unary_cont_closed dUnary zUnary nullRoute
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed nullUnary qUnary zeroRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed zeroUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row Z ∨ hsame row Q ∨ hsame row E ∨
              Cont zeroRead E sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D Z nullRead ∧ Cont nullRead Q zeroRead ∧
              Cont zeroRead E sealRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      intro _row _source
      right
      right
      right
      right
      exact sealRoute
    ledger_sound := by
      intro _row source
      exact ⟨source.right, nullRoute, zeroRoute, sealRoute, pPkg, nPkg⟩
  }
  exact ⟨cert, sealUnary⟩

end BEDC.Derived.CauchyDifferenceCriterionUp
