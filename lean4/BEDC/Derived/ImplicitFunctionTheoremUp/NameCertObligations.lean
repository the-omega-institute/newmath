import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.ImplicitFunctionTheoremUp

namespace BEDC.Derived.ImplicitFunctionTheoremUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ImplicitFunctionTheoremCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {E D I N K R _H _C _P L endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory E →
      UnaryHistory D →
        UnaryHistory N →
          UnaryHistory R →
            UnaryHistory L →
              Cont E D I →
                Cont I N K →
                  Cont K R endpoint →
                    PkgSig bundle endpoint pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row E ∨ hsame row D ∨ hsame row I ∨ hsame row N ∨
                              hsame row K ∨ hsame row R ∨ hsame row endpoint)
                          (fun row : BHist =>
                            hsame row endpoint ∧ Cont E D I ∧ Cont I N K ∧
                              Cont K R endpoint ∧ PkgSig bundle endpoint pkg)
                          hsame ∧
                        UnaryHistory I ∧ UnaryHistory K ∧ UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryE unaryD unaryN unaryR _unaryL routeEDI routeINK routeKRE endpointPkg
  have unaryI : UnaryHistory I :=
    unary_cont_closed unaryE unaryD routeEDI
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryI unaryN routeINK
  have unaryEndpoint : UnaryHistory endpoint :=
    unary_cont_closed unaryK unaryR routeKRE
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row E ∨ hsame row D ∨ hsame row I ∨ hsame row N ∨ hsame row K ∨
              hsame row R ∨ hsame row endpoint)
          (fun row : BHist =>
            hsame row endpoint ∧ Cont E D I ∧ Cont I N K ∧ Cont K R endpoint ∧
              PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint ⟨hsame_refl endpoint, unaryEndpoint⟩
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
      exact ⟨source.left, routeEDI, routeINK, routeKRE, endpointPkg⟩
  }
  exact ⟨cert, unaryI, unaryK, unaryEndpoint⟩

end BEDC.Derived.ImplicitFunctionTheoremUp
