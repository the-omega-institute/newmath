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

theorem CantorSetCarrier_triadic_window_stability [AskSetup] [PackageSetup]
    {T G I D R E H K P N prefixRead gapRead endpointRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont T G prefixRead ->
      Cont prefixRead I gapRead ->
        Cont gapRead D endpointRead ->
          Cont endpointRead R realRead ->
            PkgSig bundle N pkg ->
              UnaryHistory T ->
                UnaryHistory G ->
                  UnaryHistory I ->
                    UnaryHistory D ->
                      UnaryHistory R ->
                        SemanticNameCert
                            (fun row : BHist => hsame row prefixRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row T ∨ hsame row G ∨ hsame row prefixRead ∨
                                hsame row I ∨ hsame row gapRead ∨ hsame row D ∨
                                  hsame row endpointRead ∨ hsame row R ∨
                                    hsame row realRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont T G prefixRead ∧
                                Cont prefixRead I gapRead ∧ Cont gapRead D endpointRead ∧
                                  Cont endpointRead R realRead ∧ PkgSig bundle N pkg)
                            hsame ∧
                          UnaryHistory prefixRead ∧ UnaryHistory gapRead ∧
                            UnaryHistory endpointRead ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro prefixCont gapCont endpointCont realCont pkgN unaryT unaryG unaryI unaryD unaryR
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed unaryT unaryG prefixCont
  have gapUnary : UnaryHistory gapRead :=
    unary_cont_closed prefixUnary unaryI gapCont
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed gapUnary unaryD endpointCont
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed endpointUnary unaryR realCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row prefixRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row G ∨ hsame row prefixRead ∨ hsame row I ∨
              hsame row gapRead ∨ hsame row D ∨ hsame row endpointRead ∨ hsame row R ∨
                hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T G prefixRead ∧ Cont prefixRead I gapRead ∧
              Cont gapRead D endpointRead ∧ Cont endpointRead R realRead ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro prefixRead ⟨hsame_refl prefixRead, prefixUnary⟩
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, prefixCont, gapCont, endpointCont, realCont, pkgN⟩
  }
  exact ⟨cert, prefixUnary, gapUnary, endpointUnary, realUnary⟩

end BEDC.Derived.CantorSetUp
