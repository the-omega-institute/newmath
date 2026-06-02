import BEDC.Derived.CantorSetUp.TasteGate
import BEDC.FKernel.Package

namespace BEDC.Derived.CantorSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CantorSetScopedNestedIntervalRoute [AskSetup] [PackageSetup]
    {T G I D R E H K P N nestedRead endpointRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T ->
      UnaryHistory G ->
        UnaryHistory I ->
          UnaryHistory D ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory H ->
                  UnaryHistory K ->
                    UnaryHistory P ->
                      UnaryHistory N ->
                        Cont T G nestedRead ->
                          Cont nestedRead I endpointRead ->
                            Cont endpointRead D sealRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                      (fun row : BHist => hsame row nestedRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row T ∨ hsame row G ∨ hsame row I ∨
                                          hsame row D ∨ hsame row R ∨ hsame row E ∨
                                            hsame row H ∨ hsame row K ∨ hsame row P ∨
                                              hsame row N ∨ hsame row nestedRead ∨
                                                hsame row endpointRead ∨ hsame row sealRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont T G nestedRead ∧
                                          Cont nestedRead I endpointRead ∧
                                            Cont endpointRead D sealRead ∧
                                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory nestedRead ∧ UnaryHistory endpointRead ∧
                                      UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro unaryT unaryG unaryI unaryD _unaryR _unaryE _unaryH _unaryK _unaryP _unaryN
    nestedRoute endpointRoute sealRoute pkgP pkgN
  have nestedReadUnary : UnaryHistory nestedRead :=
    unary_cont_closed unaryT unaryG nestedRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed nestedReadUnary unaryI endpointRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointReadUnary unaryD sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nestedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row G ∨ hsame row I ∨ hsame row D ∨ hsame row R ∨
              hsame row E ∨ hsame row H ∨ hsame row K ∨ hsame row P ∨ hsame row N ∨
                hsame row nestedRead ∨ hsame row endpointRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T G nestedRead ∧ Cont nestedRead I endpointRead ∧
              Cont endpointRead D sealRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro nestedRead ⟨hsame_refl nestedRead, nestedReadUnary⟩
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
                        (Or.inr
                          (Or.inr
                            (Or.inl source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, nestedRoute, endpointRoute, sealRoute, pkgP, pkgN⟩
  }
  exact ⟨cert, nestedReadUnary, endpointReadUnary, sealReadUnary⟩

end BEDC.Derived.CantorSetUp
