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

theorem CantorSetCarrier_middle_third_window_exhaustion [AskSetup] [PackageSetup]
    {T G I D R E H K P N prefixRead gapRead endpointRead regularRead sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont T G prefixRead ->
      Cont prefixRead I gapRead ->
        Cont gapRead D endpointRead ->
          Cont endpointRead R regularRead ->
            Cont regularRead E sealedRead ->
              PkgSig bundle P pkg ->
                PkgSig bundle N pkg ->
                  UnaryHistory T ->
                    UnaryHistory G ->
                      UnaryHistory I ->
                        UnaryHistory D ->
                          UnaryHistory R ->
                            UnaryHistory E ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row gapRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row T ∨ hsame row G ∨ hsame row prefixRead ∨
                                      hsame row I ∨ hsame row gapRead ∨ hsame row D ∨
                                        hsame row endpointRead ∨ hsame row R ∨
                                          hsame row regularRead ∨ hsame row E ∨
                                            hsame row sealedRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                      PkgSig bundle N pkg ∧ Cont prefixRead I gapRead ∧
                                        Cont gapRead D endpointRead ∧
                                          Cont endpointRead R regularRead ∧
                                            Cont regularRead E sealedRead)
                                  hsame ∧
                                UnaryHistory prefixRead ∧ UnaryHistory gapRead ∧
                                  UnaryHistory endpointRead ∧ UnaryHistory regularRead ∧
                                    UnaryHistory sealedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro prefixRoute gapRoute endpointRoute regularRoute sealRoute pkgP pkgN unaryT unaryG
    unaryI unaryD unaryR unaryE
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed unaryT unaryG prefixRoute
  have gapUnary : UnaryHistory gapRead :=
    unary_cont_closed prefixUnary unaryI gapRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed gapUnary unaryD endpointRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed endpointUnary unaryR regularRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed regularUnary unaryE sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row gapRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row G ∨ hsame row prefixRead ∨ hsame row I ∨
              hsame row gapRead ∨ hsame row D ∨ hsame row endpointRead ∨ hsame row R ∨
                hsame row regularRead ∨ hsame row E ∨ hsame row sealedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
              Cont prefixRead I gapRead ∧ Cont gapRead D endpointRead ∧
                Cont endpointRead R regularRead ∧ Cont regularRead E sealedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro gapRead ⟨hsame_refl gapRead, gapUnary⟩
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
      left
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, pkgP, pkgN, gapRoute, endpointRoute, regularRoute, sealRoute⟩
  }
  exact ⟨cert, prefixUnary, gapUnary, endpointUnary, regularUnary, sealedUnary⟩

end BEDC.Derived.CantorSetUp
