import BEDC.Derived.RegularCauchyRegularityWitnessUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyRegularityWitnessUp.TasteGate

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyRegularityWitnessNameCertObligations [AskSetup] [PackageSetup]
    {S mu j Omega R Q E H C P N regularityRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S ->
      UnaryHistory mu ->
        UnaryHistory Omega ->
          UnaryHistory Q ->
            UnaryHistory H ->
              UnaryHistory P ->
                Cont S mu j ->
                  Cont j Omega R ->
                    Cont R Q E ->
                      Cont E H C ->
                        Cont C P N ->
                          Cont R Q regularityRead ->
                            Cont regularityRead E sealRead ->
                              PkgSig bundle N pkg ->
                                PkgSig bundle sealRead pkg ->
                                  SemanticNameCert
                                      (fun row : BHist => hsame row N ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row S ∨ hsame row mu ∨ hsame row j ∨
                                          hsame row Omega ∨ hsame row R ∨ hsame row Q ∨
                                            hsame row E ∨ hsame row N)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ PkgSig bundle N pkg ∧
                                          PkgSig bundle sealRead pkg)
                                      hsame ∧
                                    UnaryHistory j ∧ UnaryHistory R ∧ UnaryHistory E ∧
                                      UnaryHistory C ∧ UnaryHistory N ∧
                                        UnaryHistory regularityRead ∧
                                          UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro sUnary muUnary omegaUnary qUnary hUnary pUnary sourceIndex indexWindow
    windowTolerance sealTransport replayName regularityRoute sealRoute namePkg sealPkg
  have jUnary : UnaryHistory j :=
    unary_cont_closed sUnary muUnary sourceIndex
  have rUnary : UnaryHistory R :=
    unary_cont_closed jUnary omegaUnary indexWindow
  have eUnary : UnaryHistory E :=
    unary_cont_closed rUnary qUnary windowTolerance
  have cUnary : UnaryHistory C :=
    unary_cont_closed eUnary hUnary sealTransport
  have nUnary : UnaryHistory N :=
    unary_cont_closed cUnary pUnary replayName
  have regularityUnary : UnaryHistory regularityRead :=
    unary_cont_closed rUnary qUnary regularityRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularityUnary eUnary sealRoute
  have sourceName :
      (fun row : BHist => hsame row N ∧ UnaryHistory row) N := by
    exact ⟨hsame_refl N, nUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row mu ∨ hsame row j ∨ hsame row Omega ∨
              hsame row R ∨ hsame row Q ∨ hsame row E ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle N pkg ∧ PkgSig bundle sealRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro N sourceName
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, namePkg, sealPkg⟩
    }
  exact
    ⟨cert, jUnary, rUnary, eUnary, cUnary, nUnary, regularityUnary, sealUnary⟩

end BEDC.Derived.RegularCauchyRegularityWitnessUp.TasteGate
