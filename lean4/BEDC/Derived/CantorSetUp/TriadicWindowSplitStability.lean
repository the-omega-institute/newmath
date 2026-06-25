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

theorem CantorSetCarrier_triadic_window_split_stability [AskSetup] [PackageSetup]
    {T G I D R E H K P N T2 G2 I2 D2 R2 E2 H2 K2 P2 N2 prefixRead prefixRead2
      gapRead gapRead2 endpointRead endpointRead2 regularRead regularRead2 sealedRead
      sealedRead2 splitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont T G prefixRead ->
      Cont T2 G2 prefixRead2 ->
        hsame prefixRead prefixRead2 ->
          Cont prefixRead I gapRead ->
            Cont prefixRead2 I2 gapRead2 ->
              hsame gapRead gapRead2 ->
                Cont gapRead D endpointRead ->
                  Cont gapRead2 D2 endpointRead2 ->
                    Cont endpointRead R regularRead ->
                      Cont endpointRead2 R2 regularRead2 ->
                        Cont regularRead E sealedRead ->
                          Cont regularRead2 E2 sealedRead2 ->
                            Cont gapRead gapRead2 splitRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle P2 pkg ->
                                  UnaryHistory T ->
                                    UnaryHistory G ->
                                      UnaryHistory I ->
                                        UnaryHistory D ->
                                          UnaryHistory R ->
                                            UnaryHistory E ->
                                              UnaryHistory T2 ->
                                                UnaryHistory G2 ->
                                                  UnaryHistory I2 ->
                                                    UnaryHistory D2 ->
                                                      UnaryHistory R2 ->
                                                        UnaryHistory E2 ->
                                                          SemanticNameCert
                                                              (fun row : BHist =>
                                                                hsame row splitRead ∧
                                                                  UnaryHistory row)
                                                              (fun row : BHist =>
                                                                hsame row gapRead ∨
                                                                  hsame row gapRead2 ∨
                                                                    hsame row splitRead ∨
                                                                      hsame row sealedRead ∨
                                                                        hsame row sealedRead2)
                                                              (fun row : BHist =>
                                                                UnaryHistory row ∧
                                                                  Cont gapRead gapRead2
                                                                    splitRead ∧
                                                                    PkgSig bundle P pkg ∧
                                                                      PkgSig bundle P2 pkg)
                                                              hsame ∧
                                                            UnaryHistory splitRead ∧
                                                              hsame prefixRead prefixRead2 ∧
                                                                hsame gapRead gapRead2 := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro prefixCont prefixCont2 prefixSame gapCont gapCont2 gapSame endpointCont
    endpointCont2 regularCont regularCont2 sealedCont sealedCont2 splitCont pkgP pkgP2
    unaryT unaryG unaryI unaryD unaryR unaryE unaryT2 unaryG2 unaryI2 unaryD2 unaryR2
    unaryE2
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed unaryT unaryG prefixCont
  have prefixUnary2 : UnaryHistory prefixRead2 :=
    unary_cont_closed unaryT2 unaryG2 prefixCont2
  have gapUnary : UnaryHistory gapRead :=
    unary_cont_closed prefixUnary unaryI gapCont
  have gapUnary2 : UnaryHistory gapRead2 :=
    unary_cont_closed prefixUnary2 unaryI2 gapCont2
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed gapUnary unaryD endpointCont
  have endpointUnary2 : UnaryHistory endpointRead2 :=
    unary_cont_closed gapUnary2 unaryD2 endpointCont2
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed endpointUnary unaryR regularCont
  have regularUnary2 : UnaryHistory regularRead2 :=
    unary_cont_closed endpointUnary2 unaryR2 regularCont2
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed regularUnary unaryE sealedCont
  have sealedUnary2 : UnaryHistory sealedRead2 :=
    unary_cont_closed regularUnary2 unaryE2 sealedCont2
  have splitUnary : UnaryHistory splitRead :=
    unary_cont_closed gapUnary gapUnary2 splitCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row splitRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row gapRead ∨ hsame row gapRead2 ∨ hsame row splitRead ∨
              hsame row sealedRead ∨ hsame row sealedRead2)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont gapRead gapRead2 splitRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle P2 pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro splitRead ⟨hsame_refl splitRead, splitUnary⟩
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
      exact ⟨source.right, splitCont, pkgP, pkgP2⟩
  }
  exact ⟨cert, splitUnary, prefixSame, gapSame⟩

end BEDC.Derived.CantorSetUp
