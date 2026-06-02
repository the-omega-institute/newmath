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

theorem CantorSetCarrier_ternary_prefix_density [AskSetup] [PackageSetup]
    {T G I D R E _H _K _P N endpointRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont T G I ->
      Cont I D endpointRead ->
        Cont endpointRead R realRead ->
          PkgSig bundle N pkg ->
            UnaryHistory T ->
              UnaryHistory G ->
                UnaryHistory D ->
                  UnaryHistory R ->
                    SemanticNameCert
                        (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row T ∨ hsame row G ∨ hsame row I ∨ hsame row D ∨
                            hsame row R ∨ hsame row E ∨ hsame row endpointRead ∨
                              hsame row realRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont T G I ∧ Cont I D endpointRead ∧
                            Cont endpointRead R realRead ∧ PkgSig bundle N pkg)
                        hsame ∧
                      UnaryHistory I ∧ UnaryHistory endpointRead ∧
                        UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro intervalCont endpointCont realCont pkgN unaryT unaryG unaryD unaryR
  have intervalUnary : UnaryHistory I :=
    unary_cont_closed unaryT unaryG intervalCont
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed intervalUnary unaryD endpointCont
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed endpointUnary unaryR realCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row G ∨ hsame row I ∨ hsame row D ∨ hsame row R ∨
              hsame row E ∨ hsame row endpointRead ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T G I ∧ Cont I D endpointRead ∧
              Cont endpointRead R realRead ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro endpointRead ⟨hsame_refl endpointRead, endpointUnary⟩
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
      right
      right
      right
      right
      right
      right
      left
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, intervalCont, endpointCont, realCont, pkgN⟩
  }
  exact ⟨cert, intervalUnary, endpointUnary, realUnary⟩

end BEDC.Derived.CantorSetUp
