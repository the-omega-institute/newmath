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

theorem CantorSetCarrier_nested_real_handoff [AskSetup] [PackageSetup]
    {T G I D R E H K P N endpointRead realRead sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont T G I ->
      Cont I D endpointRead ->
        Cont endpointRead R realRead ->
          Cont realRead E sealedRead ->
            PkgSig bundle N pkg ->
              UnaryHistory T ->
                UnaryHistory G ->
                  UnaryHistory D ->
                    UnaryHistory R ->
                      UnaryHistory E ->
                        SemanticNameCert
                            (fun row : BHist => hsame row E ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row T ∨ hsame row G ∨ hsame row I ∨ hsame row D ∨
                                hsame row R ∨ hsame row E ∨ hsame row N)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont T G I ∧ Cont I D endpointRead ∧
                                Cont endpointRead R realRead ∧ Cont realRead E sealedRead ∧
                                  PkgSig bundle N pkg)
                            hsame ∧
                          UnaryHistory I ∧ UnaryHistory endpointRead ∧
                            UnaryHistory realRead ∧ UnaryHistory sealedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro intervalRoute endpointRoute realRoute sealRoute packageN prefixUnary gapUnary
    endpointUnary realUnary sealUnary
  have intervalUnary : UnaryHistory I :=
    unary_cont_closed prefixUnary gapUnary intervalRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed intervalUnary endpointUnary endpointRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed endpointReadUnary realUnary realRoute
  have sealedReadUnary : UnaryHistory sealedRead :=
    unary_cont_closed realReadUnary sealUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row E ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row G ∨ hsame row I ∨ hsame row D ∨ hsame row R ∨
              hsame row E ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T G I ∧ Cont I D endpointRead ∧
              Cont endpointRead R realRead ∧ Cont realRead E sealedRead ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro E ⟨hsame_refl E, sealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, intervalRoute, endpointRoute, realRoute, sealRoute, packageN⟩
  }
  exact ⟨cert, intervalUnary, endpointReadUnary, realReadUnary, sealedReadUnary⟩

end BEDC.Derived.CantorSetUp
