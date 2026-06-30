import BEDC.Derived.RegularCauchyRegularityWitnessUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyRegularityWitnessUp

def RegularCauchyRegularityWitnessCarrier [AskSetup] [PackageSetup]
    (S mu j Omega R Q E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory S ∧ UnaryHistory mu ∧ UnaryHistory j ∧ UnaryHistory Omega ∧
    UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory E ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ Cont S mu j ∧
        Cont j Omega R ∧ Cont R Q E ∧ Cont E H C ∧ PkgSig bundle P pkg ∧
          PkgSig bundle N pkg

theorem RegularCauchyRegularityWitness_namecert_obligations [AskSetup] [PackageSetup]
    {S mu j Omega R Q E H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyRegularityWitnessCarrier S mu j Omega R Q E H C P N bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row mu ∨ hsame row j ∨ hsame row Omega ∨
              hsame row R ∨ hsame row Q ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S mu j ∧ Cont j Omega R ∧ Cont R Q E ∧
              Cont E H C ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame ∧
        UnaryHistory N := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier
  obtain ⟨_unaryS, _unaryMu, _unaryJ, _unaryOmega, _unaryR, _unaryQ, _unaryE,
    _unaryH, _unaryC, _unaryP, unaryN, routeSMuJ, routeJOmegaR, routeRQE,
    routeEHC, pkgP, pkgN⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row mu ∨ hsame row j ∨ hsame row Omega ∨
              hsame row R ∨ hsame row Q ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S mu j ∧ Cont j Omega R ∧ Cont R Q E ∧
              Cont E H C ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, unaryN⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeSMuJ, routeJOmegaR, routeRQE, routeEHC, pkgP, pkgN⟩
  }
  exact ⟨cert, unaryN⟩

end BEDC.Derived.RegularCauchyRegularityWitnessUp

namespace BEDC.Derived.RegularCauchyRegularityWitnessUp.TasteGate

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
