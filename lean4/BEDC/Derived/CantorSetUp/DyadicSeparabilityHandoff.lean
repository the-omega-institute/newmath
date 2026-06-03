import BEDC.Derived.CantorSetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CantorSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CantorSetDyadicSeparabilityHandoff [AskSetup] [PackageSetup]
    {T G I D R E H K P N dyadicRead separabilityRead sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory G →
        UnaryHistory D →
          UnaryHistory R →
            UnaryHistory E →
              Cont T G I →
                Cont I D dyadicRead →
                  Cont dyadicRead R separabilityRead →
                    Cont separabilityRead E sealedRead →
                      PkgSig bundle P pkg →
                        PkgSig bundle N pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row T ∨ hsame row G ∨ hsame row I ∨
                                  hsame row D ∨ hsame row R ∨ hsame row E ∨
                                    hsame row sealedRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont T G I ∧
                                  Cont I D dyadicRead ∧
                                    Cont dyadicRead R separabilityRead ∧
                                      Cont separabilityRead E sealedRead ∧
                                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                              hsame ∧
                            UnaryHistory I ∧ UnaryHistory dyadicRead ∧
                              UnaryHistory separabilityRead ∧ UnaryHistory sealedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro unaryT unaryG unaryD unaryR unaryE routeInterval routeDyadic routeSeparability
    routeSealed pkgP pkgN
  have unaryI : UnaryHistory I :=
    unary_cont_closed unaryT unaryG routeInterval
  have unaryDyadic : UnaryHistory dyadicRead :=
    unary_cont_closed unaryI unaryD routeDyadic
  have unarySeparability : UnaryHistory separabilityRead :=
    unary_cont_closed unaryDyadic unaryR routeSeparability
  have unarySealed : UnaryHistory sealedRead :=
    unary_cont_closed unarySeparability unaryE routeSealed
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row G ∨ hsame row I ∨ hsame row D ∨ hsame row R ∨
              hsame row E ∨ hsame row sealedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T G I ∧ Cont I D dyadicRead ∧
              Cont dyadicRead R separabilityRead ∧ Cont separabilityRead E sealedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealedRead ⟨hsame_refl sealedRead, unarySealed⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeInterval, routeDyadic, routeSeparability, routeSealed, pkgP,
          pkgN⟩
  }
  exact ⟨cert, unaryI, unaryDyadic, unarySeparability, unarySealed⟩

end BEDC.Derived.CantorSetUp
